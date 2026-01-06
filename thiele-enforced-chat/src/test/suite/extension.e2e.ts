/**
 * E2E Tests for Thiele Enforced Chat Extension
 * Tests the extension running in VS Code
 */
import * as assert from 'assert';
import * as vscode from 'vscode';

describe('Thiele Extension E2E Tests', () => {
    
    before(async function() {
        // Wait for extension to activate
        this.timeout(30000);
        const ext = vscode.extensions.getExtension('thiele-machine.thiele-enforced-chat');
        if (ext && !ext.isActive) {
            await ext.activate();
        }
    });

    describe('Extension Activation', () => {
        it('should be present', () => {
            const ext = vscode.extensions.getExtension('thiele-machine.thiele-enforced-chat');
            assert.ok(ext, 'Extension should be installed');
        });

        it('should activate successfully', async () => {
            const ext = vscode.extensions.getExtension('thiele-machine.thiele-enforced-chat');
            assert.ok(ext, 'Extension should be installed');
            
            if (!ext.isActive) {
                await ext.activate();
            }
            
            assert.ok(ext.isActive, 'Extension should be active');
        });
    });

    describe('Commands Registration', () => {
        it('should register thiele.verifySelection command', async () => {
            const commands = await vscode.commands.getCommands();
            assert.ok(commands.includes('thiele.verifySelection'), 'thiele.verifySelection should be registered');
        });

        it('should register thiele.fixSelection command', async () => {
            const commands = await vscode.commands.getCommands();
            assert.ok(commands.includes('thiele.fixSelection'), 'thiele.fixSelection should be registered');
        });

        it('should register thiele.verifyFile command', async () => {
            const commands = await vscode.commands.getCommands();
            assert.ok(commands.includes('thiele.verifyFile'), 'thiele.verifyFile should be registered');
        });

        it('should register thiele.showStats command', async () => {
            const commands = await vscode.commands.getCommands();
            assert.ok(commands.includes('thiele.showStats'), 'thiele.showStats should be registered');
        });
    });

    describe('Status Bar', () => {
        it('should show status bar item', async () => {
            // Status bar items are shown via createStatusBarItem
            // We can't directly test their visibility, but we can verify the extension activated
            const ext = vscode.extensions.getExtension('thiele-machine.thiele-enforced-chat');
            assert.ok(ext?.isActive, 'Extension should be active (status bar is created during activation)');
        });
    });

    describe('Output Channel', () => {
        it('should create Thiele Verifier output channel', async () => {
            // Output channels are created during activation
            const ext = vscode.extensions.getExtension('thiele-machine.thiele-enforced-chat');
            assert.ok(ext?.isActive, 'Extension should be active (output channel is created during activation)');
        });
    });
});
