import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';
import { exec } from 'child_process';

export function activate(context: vscode.ExtensionContext) {
    console.log('Thiele Machine Verilog Simulator extension is now active!');

    // Clear Environment Cache
    let clearCacheDisposable = vscode.commands.registerCommand('verilog-simulator.clearCache', async () => {
        const workspaceFolder = vscode.workspace.workspaceFolders?.[0];
        if (!workspaceFolder) {
            vscode.window.showErrorMessage('No workspace folder open');
            return;
        }

        const cacheDir = path.join(workspaceFolder.uri.fsPath, 'thielecpu', 'hardware', '.verilog_cache');
        
        try {
            if (fs.existsSync(cacheDir)) {
                fs.rmSync(cacheDir, { recursive: true, force: true });
                vscode.window.showInformationMessage('Verilog simulation cache cleared');
            } else {
                vscode.window.showInformationMessage('No cache directory found');
            }
        } catch (error) {
            vscode.window.showErrorMessage(`Failed to clear cache: ${error}`);
        }
    });

    // Generate Waveform
    let generateWaveformDisposable = vscode.commands.registerCommand('verilog-simulator.generateWaveform', async () => {
        const workspaceFolder = vscode.workspace.workspaceFolders?.[0];
        if (!workspaceFolder) {
            vscode.window.showErrorMessage('No workspace folder open');
            return;
        }

        const activeEditor = vscode.window.activeTextEditor;
        if (!activeEditor || !activeEditor.document.fileName.endsWith('.v')) {
            vscode.window.showErrorMessage('Please open a Verilog file (.v)');
            return;
        }

        const verilogFile = activeEditor.document.fileName;
        const baseName = path.basename(verilogFile, '.v');
        const hardwareDir = path.dirname(verilogFile);
        
        // Check if this is a testbench file
        const isTestbench = baseName.includes('tb') || baseName.includes('test');
        
        if (!isTestbench) {
            vscode.window.showErrorMessage('Please select a testbench file (containing "tb" or "test" in filename)');
            return;
        }

        // Run simulation and generate VCD
        const vvpFile = path.join(hardwareDir, `${baseName}.vvp`);
        const vcdFile = path.join(hardwareDir, `${baseName}.vcd`);
        
        // Compile with iverilog
        const compileCommand = `cd "${hardwareDir}" && iverilog -g2012 -o "${vvpFile}" "${verilogFile}"`;
        
        vscode.window.withProgress({
            location: vscode.ProgressLocation.Notification,
            title: 'Compiling Verilog...',
            cancellable: false
        }, async (progress) => {
            progress.report({ increment: 0, message: 'Compiling...' });
            
            return new Promise<void>((resolve, reject) => {
                exec(compileCommand, (error, stdout, stderr) => {
                    if (error) {
                        vscode.window.showErrorMessage(`Compilation failed: ${stderr}`);
                        reject(error);
                        return;
                    }
                    
                    progress.report({ increment: 50, message: 'Running simulation...' });
                    
                    // Run simulation
                    const runCommand = `cd "${hardwareDir}" && vvp "${vvpFile}"`;
                    
                    exec(runCommand, (error, stdout, stderr) => {
                        if (error) {
                            vscode.window.showErrorMessage(`Simulation failed: ${stderr}`);
                            reject(error);
                            return;
                        }
                        
                        progress.report({ increment: 100, message: 'Complete!' });
                        
                        // Check if VCD was generated
                        if (fs.existsSync(vcdFile)) {
                            vscode.window.showInformationMessage(`Waveform generated: ${baseName}.vcd`);
                            
                            // Try to open with GTKWave if available
                            exec(`gtkwave "${vcdFile}"`, (error) => {
                                if (error) {
                                    vscode.window.showWarningMessage('GTKWave not found. Install GTKWave to view waveforms graphically.');
                                }
                            });
                        } else {
                            vscode.window.showWarningMessage('Simulation completed but no VCD file generated');
                        }
                        
                        resolve();
                    });
                });
            });
        });
    });

    // Regenerate VCD File (Robust Mode)
    let regenerateVcdDisposable = vscode.commands.registerCommand('verilog-simulator.regenerateVcd', async () => {
        const workspaceFolder = vscode.workspace.workspaceFolders?.[0];
        if (!workspaceFolder) {
            vscode.window.showErrorMessage('No workspace folder open');
            return;
        }

        const activeEditor = vscode.window.activeTextEditor;
        if (!activeEditor || !activeEditor.document.fileName.endsWith('.v')) {
            vscode.window.showErrorMessage('Please open a Verilog file (.v)');
            return;
        }

        const verilogFile = activeEditor.document.fileName;
        const baseName = path.basename(verilogFile, '.v');
        const hardwareDir = path.dirname(verilogFile);
        
        // Robust mode: clean everything and rebuild
        const vvpFile = path.join(hardwareDir, `${baseName}.vvp`);
        const vcdFile = path.join(hardwareDir, `${baseName}.vcd`);
        
        vscode.window.withProgress({
            location: vscode.ProgressLocation.Notification,
            title: 'Regenerating VCD (Robust Mode)...',
            cancellable: false
        }, async (progress) => {
            progress.report({ increment: 0, message: 'Cleaning old files...' });
            
            // Clean old files
            [vvpFile, vcdFile].forEach(file => {
                if (fs.existsSync(file)) {
                    fs.unlinkSync(file);
                }
            });
            
            progress.report({ increment: 20, message: 'Finding dependencies...' });
            
            // Find all Verilog files in hardware directory for dependencies
            const verilogFiles = fs.readdirSync(hardwareDir)
                .filter(file => file.endsWith('.v'))
                .map(file => path.join(hardwareDir, file));
            
            progress.report({ increment: 40, message: 'Compiling with dependencies...' });
            
            // Compile with all dependencies
            const compileCommand = `cd "${hardwareDir}" && iverilog -g2012 -o "${vvpFile}" ${verilogFiles.map(f => `"${f}"`).join(' ')}`;
            
            return new Promise<void>((resolve, reject) => {
                exec(compileCommand, (error, stdout, stderr) => {
                    if (error) {
                        vscode.window.showErrorMessage(`Robust compilation failed: ${stderr}`);
                        reject(error);
                        return;
                    }
                    
                    progress.report({ increment: 70, message: 'Running simulation...' });
                    
                    // Run simulation with VCD dump
                    const runCommand = `cd "${hardwareDir}" && vvp "${vvpFile}"`;
                    
                    exec(runCommand, (error, stdout, stderr) => {
                        if (error) {
                            vscode.window.showErrorMessage(`Robust simulation failed: ${stderr}`);
                            reject(error);
                            return;
                        }
                        
                        progress.report({ increment: 100, message: 'Complete!' });
                        
                        if (fs.existsSync(vcdFile)) {
                            vscode.window.showInformationMessage(`VCD regenerated successfully: ${baseName}.vcd`);
                        } else {
                            vscode.window.showWarningMessage('Simulation completed but VCD file not found');
                        }
                        
                        resolve();
                    });
                });
            });
        });
    });

    context.subscriptions.push(clearCacheDisposable);
    context.subscriptions.push(generateWaveformDisposable);
    context.subscriptions.push(regenerateVcdDisposable);
}

export function deactivate() {}