#!/usr/bin/env python3
"""
Thiele Receipt Watcher - Auto-generate receipts on file changes

This tool watches your project directory and automatically regenerates
receipts when build artifacts change. Perfect for local development.

Usage:
    thiele-watch
    thiele-watch --project /path/to/project
    thiele-watch --sign signing.key
    thiele-watch --debounce 5
"""

import argparse
import sys
import time
import hashlib
import json
from pathlib import Path
from datetime import datetime
from typing import Set, Dict, Optional
import subprocess

# Try to import watchdog for file system monitoring
try:
    from watchdog.observers import Observer
    from watchdog.events import FileSystemEventHandler, FileSystemEvent
    HAS_WATCHDOG = True
except ImportError:
    HAS_WATCHDOG = False
    print("Warning: watchdog not installed. Install with: pip install watchdog")
    print("Falling back to polling mode...")


class ReceiptWatcher(FileSystemEventHandler):
    """Watch for changes to build artifacts and regenerate receipts."""
    
    def __init__(
        self,
        project_dir: Path,
        output_dir: Path,
        sign_key: Optional[Path] = None,
        public_key: Optional[Path] = None,
        debounce: float = 2.0,
        verbose: bool = False
    ):
        self.project_dir = project_dir.resolve()
        self.output_dir = output_dir.resolve()
        self.sign_key = sign_key
        self.public_key = public_key
        self.debounce = debounce
        self.verbose = verbose
        
        # Track file hashes to detect real changes
        self.file_hashes: Dict[Path, str] = {}
        
        # Track pending regenerations to debounce
        self.pending_regen = False
        self.last_regen_time = 0
        
        # Directories to watch
        self.watch_dirs = [
            'dist', 'target', 'build', 'bin', 'pkg',
            'out', 'releases', 'artifacts'
        ]
        
        print(f"📂 Watching project: {self.project_dir}")
        print(f"💾 Output directory: {self.output_dir}")
        if self.sign_key:
            print(f"🔑 Signing enabled: {self.sign_key}")
        print(f"⏱️  Debounce: {self.debounce}s")
        print()
        
        # Do initial scan
        self._scan_artifacts()
    
    def _scan_artifacts(self) -> Set[Path]:
        """Scan for build artifacts in watch directories."""
        artifacts = set()
        
        for watch_dir in self.watch_dirs:
            dir_path = self.project_dir / watch_dir
            if not dir_path.exists():
                continue
            
            # Common artifact extensions
            patterns = [
                '*.whl', '*.tar.gz', '*.zip', '*.exe', '*.dll',
                '*.so', '*.dylib', '*.jar', '*.war', '*.AppImage',
                '*.deb', '*.rpm', '*.dmg'
            ]
            
            for pattern in patterns:
                for artifact in dir_path.glob(f"**/{pattern}"):
                    if artifact.is_file():
                        artifacts.add(artifact)
        
        return artifacts
    
    def _compute_hash(self, filepath: Path) -> str:
        """Compute SHA256 hash of a file."""
        sha256 = hashlib.sha256()
        with open(filepath, 'rb') as f:
            for chunk in iter(lambda: f.read(4096), b''):
                sha256.update(chunk)
        return sha256.hexdigest()
    
    def _has_changed(self, filepath: Path) -> bool:
        """Check if file has actually changed (not just modified timestamp)."""
        if not filepath.exists():
            # File was deleted
            if filepath in self.file_hashes:
                del self.file_hashes[filepath]
            return True
        
        current_hash = self._compute_hash(filepath)
        previous_hash = self.file_hashes.get(filepath)
        
        if previous_hash != current_hash:
            self.file_hashes[filepath] = current_hash
            return True
        
        return False
    
    def _should_regenerate(self, filepath: Path) -> bool:
        """Check if this file change should trigger regeneration."""
        # Skip if not in a watched directory
        try:
            rel_path = filepath.relative_to(self.project_dir)
            if not any(str(rel_path).startswith(d) for d in self.watch_dirs):
                return False
        except ValueError:
            return False
        
        # Skip receipt files themselves
        if filepath.suffix == '.json' and 'receipt' in filepath.name:
            return False
        
        # Check if file actually changed
        return self._has_changed(filepath)
    
    def _regenerate_receipts(self):
        """Regenerate receipts for all artifacts."""
        now = time.time()
        
        # Debounce rapid changes
        if now - self.last_regen_time < self.debounce:
            if not self.pending_regen:
                self.pending_regen = True
                if self.verbose:
                    print(f"⏳ Debouncing... waiting {self.debounce}s")
            return
        
        self.pending_regen = False
        self.last_regen_time = now
        
        print(f"\n🔄 Regenerating receipts... ({datetime.now().strftime('%H:%M:%S')})")
        
        # Build command
        cmd = [
            'python3', 'create_receipt.py',
            '--project', str(self.project_dir),
            '--output', str(self.output_dir)
        ]
        
        if self.sign_key:
            cmd.extend(['--sign', str(self.sign_key)])
        
        if self.public_key:
            cmd.extend(['--public-key', str(self.public_key)])
        
        try:
            # Run receipt generation
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=30
            )
            
            if result.returncode == 0:
                # Count receipts
                receipts = list(self.output_dir.glob('*.receipt.json'))
                manifest = self.output_dir / 'MANIFEST.receipt.json'
                if manifest.exists():
                    receipts.remove(manifest)
                
                print(f"✅ Created {len(receipts)} receipt(s)")
                if self.verbose:
                    print(result.stdout)
            else:
                print(f"❌ Failed to generate receipts")
                print(result.stderr)
        
        except subprocess.TimeoutExpired:
            print(f"❌ Receipt generation timed out")
        except Exception as e:
            print(f"❌ Error: {e}")
    
    def on_modified(self, event: FileSystemEvent):
        """Handle file modification events."""
        if event.is_directory:
            return
        
        filepath = Path(event.src_path)
        
        if self._should_regenerate(filepath):
            if self.verbose:
                print(f"📝 Changed: {filepath.name}")
            self._regenerate_receipts()
    
    def on_created(self, event: FileSystemEvent):
        """Handle file creation events."""
        if event.is_directory:
            return
        
        filepath = Path(event.src_path)
        
        if self._should_regenerate(filepath):
            if self.verbose:
                print(f"➕ Created: {filepath.name}")
            self._regenerate_receipts()
    
    def on_deleted(self, event: FileSystemEvent):
        """Handle file deletion events."""
        if event.is_directory:
            return
        
        filepath = Path(event.src_path)
        
        if self._should_regenerate(filepath):
            if self.verbose:
                print(f"🗑️  Deleted: {filepath.name}")
            self._regenerate_receipts()


def watch_with_watchdog(watcher: ReceiptWatcher):
    """Watch using watchdog library (preferred)."""
    observer = Observer()
    
    # Watch each directory
    for watch_dir in watcher.watch_dirs:
        dir_path = watcher.project_dir / watch_dir
        if dir_path.exists():
            observer.schedule(watcher, str(dir_path), recursive=True)
            print(f"👀 Watching: {watch_dir}/")
    
    observer.start()
    
    try:
        print("\n✓ Watcher started. Press Ctrl+C to stop.\n")
        while True:
            time.sleep(1)
            
            # Check if we need to process pending regeneration
            if watcher.pending_regen:
                now = time.time()
                if now - watcher.last_regen_time >= watcher.debounce:
                    watcher._regenerate_receipts()
    
    except KeyboardInterrupt:
        print("\n\n⏹️  Stopping watcher...")
        observer.stop()
    
    observer.join()


def watch_with_polling(watcher: ReceiptWatcher, interval: float = 5.0):
    """Watch using simple polling (fallback)."""
    print(f"👀 Polling every {interval}s (install 'watchdog' for better performance)")
    print("✓ Watcher started. Press Ctrl+C to stop.\n")
    
    try:
        while True:
            artifacts = watcher._scan_artifacts()
            
            for artifact in artifacts:
                if watcher._has_changed(artifact):
                    if watcher.verbose:
                        print(f"📝 Changed: {artifact.name}")
                    watcher._regenerate_receipts()
                    break  # Only regenerate once per cycle
            
            time.sleep(interval)
    
    except KeyboardInterrupt:
        print("\n\n⏹️  Stopping watcher...")


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description='Watch for changes and auto-generate receipts',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s
  %(prog)s --project /path/to/myproject
  %(prog)s --sign signing.key --verbose
  %(prog)s --debounce 5 --poll-interval 10
        """
    )
    
    parser.add_argument(
        '--project',
        type=Path,
        default=Path('.'),
        help='Project directory to watch (default: current directory)'
    )
    
    parser.add_argument(
        '--output',
        type=Path,
        default=Path('receipts'),
        help='Output directory for receipts (default: receipts)'
    )
    
    parser.add_argument(
        '--sign',
        type=Path,
        help='Ed25519 private key for signing (optional)'
    )
    
    parser.add_argument(
        '--public-key',
        type=Path,
        help='Ed25519 public key (optional)'
    )
    
    parser.add_argument(
        '--debounce',
        type=float,
        default=2.0,
        help='Debounce time in seconds (default: 2.0)'
    )
    
    parser.add_argument(
        '--poll-interval',
        type=float,
        default=5.0,
        help='Polling interval in seconds when watchdog unavailable (default: 5.0)'
    )
    
    parser.add_argument(
        '--verbose',
        action='store_true',
        help='Verbose output'
    )
    
    args = parser.parse_args()
    
    # Create watcher
    watcher = ReceiptWatcher(
        project_dir=args.project,
        output_dir=args.output,
        sign_key=args.sign,
        public_key=args.public_key,
        debounce=args.debounce,
        verbose=args.verbose
    )
    
    # Use watchdog if available, otherwise fall back to polling
    if HAS_WATCHDOG:
        watch_with_watchdog(watcher)
    else:
        watch_with_polling(watcher, args.poll_interval)


if __name__ == '__main__':
    main()
