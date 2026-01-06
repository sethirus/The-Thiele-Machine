import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';
import {
    CodeBlock,
    VerifierClient,
    ThieleVerifierClient,
    extractCodeBlocks,
    shouldSkipLanguage,
    detectLanguage,
    formatTableRow,
    OrganicVerificationResult
} from './verifier';

let outputChannel: vscode.OutputChannel;
let verifierClient: VerifierClient;

/**
 * Set a custom verifier client (for testing)
 */
export function setVerifierClient(client: VerifierClient) {
    verifierClient = client;
}

/**
 * Get the current verifier client
 */
export function getVerifierClient(): VerifierClient {
    return verifierClient;
}

// ═══════════════════════════════════════════════════════════════════════════
// 🧠 AGENTIC FILE PLACEMENT TOOLS
// These tools allow the LLM to intelligently determine where files should go
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Tool: Analyze workspace structure to determine appropriate file locations
 */
class WorkspaceStructureTool implements vscode.LanguageModelTool<{ path?: string }> {
    async invoke(
        options: vscode.LanguageModelToolInvocationOptions<{ path?: string }>,
        token: vscode.CancellationToken
    ): Promise<vscode.LanguageModelToolResult> {
        const wsFolder = vscode.workspace.workspaceFolders?.[0];
        if (!wsFolder) {
            return new vscode.LanguageModelToolResult([
                new vscode.LanguageModelTextPart('No workspace folder open')
            ]);
        }

        const basePath = options.input?.path 
            ? path.join(wsFolder.uri.fsPath, options.input.path)
            : wsFolder.uri.fsPath;

        try {
            const structure = await this.getDirectoryStructure(basePath, 3);
            return new vscode.LanguageModelToolResult([
                new vscode.LanguageModelTextPart(JSON.stringify(structure, null, 2))
            ]);
        } catch (e) {
            return new vscode.LanguageModelToolResult([
                new vscode.LanguageModelTextPart(`Error reading workspace: ${e}`)
            ]);
        }
    }

    private async getDirectoryStructure(dir: string, depth: number): Promise<any> {
        if (depth === 0) return { truncated: true };
        
        const result: any = {};
        const entries = fs.readdirSync(dir, { withFileTypes: true });
        
        for (const entry of entries) {
            // Skip hidden, node_modules, __pycache__, .git
            if (entry.name.startsWith('.') || 
                entry.name === 'node_modules' || 
                entry.name === '__pycache__' ||
                entry.name === 'build' ||
                entry.name === 'dist') continue;
            
            if (entry.isDirectory()) {
                result[entry.name + '/'] = await this.getDirectoryStructure(
                    path.join(dir, entry.name), 
                    depth - 1
                );
            } else {
                result[entry.name] = 'file';
            }
        }
        return result;
    }
}

/**
 * Tool: Find similar files to determine patterns
 */
class FindSimilarFilesTool implements vscode.LanguageModelTool<{ pattern: string; extension: string }> {
    async invoke(
        options: vscode.LanguageModelToolInvocationOptions<{ pattern: string; extension: string }>,
        token: vscode.CancellationToken
    ): Promise<vscode.LanguageModelToolResult> {
        const { pattern, extension } = options.input;
        const wsFolder = vscode.workspace.workspaceFolders?.[0];
        
        if (!wsFolder) {
            return new vscode.LanguageModelToolResult([
                new vscode.LanguageModelTextPart('No workspace folder open')
            ]);
        }

        try {
            const files = await vscode.workspace.findFiles(
                `**/*${extension}`,
                '**/node_modules/**',
                50
            );
            
            const matchingFiles = files
                .map(f => vscode.workspace.asRelativePath(f))
                .filter(f => f.toLowerCase().includes(pattern.toLowerCase()))
                .slice(0, 10);
            
            // Group by directory
            const byDir: Record<string, string[]> = {};
            for (const f of matchingFiles) {
                const dir = path.dirname(f);
                if (!byDir[dir]) byDir[dir] = [];
                byDir[dir].push(path.basename(f));
            }
            
            return new vscode.LanguageModelToolResult([
                new vscode.LanguageModelTextPart(JSON.stringify({
                    matchingFiles,
                    byDirectory: byDir,
                    totalFound: files.length
                }, null, 2))
            ]);
        } catch (e) {
            return new vscode.LanguageModelToolResult([
                new vscode.LanguageModelTextPart(`Error: ${e}`)
            ]);
        }
    }
}

/**
 * Tool: Create file at specified path
 */
class CreateFileTool implements vscode.LanguageModelTool<{ filePath: string; content: string }> {
    async invoke(
        options: vscode.LanguageModelToolInvocationOptions<{ filePath: string; content: string }>,
        token: vscode.CancellationToken
    ): Promise<vscode.LanguageModelToolResult> {
        const { filePath, content } = options.input;
        const wsFolder = vscode.workspace.workspaceFolders?.[0];
        
        if (!wsFolder) {
            return new vscode.LanguageModelToolResult([
                new vscode.LanguageModelTextPart('No workspace folder open')
            ]);
        }

        const absolutePath = path.isAbsolute(filePath) 
            ? filePath 
            : path.join(wsFolder.uri.fsPath, filePath);
        
        try {
            // Create directory if needed
            const dir = path.dirname(absolutePath);
            if (!fs.existsSync(dir)) {
                fs.mkdirSync(dir, { recursive: true });
            }
            
            // Write file
            fs.writeFileSync(absolutePath, content);
            
            // Open in editor
            const uri = vscode.Uri.file(absolutePath);
            const doc = await vscode.workspace.openTextDocument(uri);
            await vscode.window.showTextDocument(doc, { 
                preview: false, 
                viewColumn: vscode.ViewColumn.Beside 
            });
            
            return new vscode.LanguageModelToolResult([
                new vscode.LanguageModelTextPart(`✅ Created: ${filePath}`)
            ]);
        } catch (e) {
            return new vscode.LanguageModelToolResult([
                new vscode.LanguageModelTextPart(`❌ Error creating file: ${e}`)
            ]);
        }
    }

    async prepareInvocation(
        options: vscode.LanguageModelToolInvocationPrepareOptions<{ filePath: string; content: string }>,
        token: vscode.CancellationToken
    ): Promise<vscode.PreparedToolInvocation> {
        return {
            invocationMessage: `Creating file: ${options.input.filePath}`,
            confirmationMessages: {
                title: 'Create File',
                message: new vscode.MarkdownString(`Create **${options.input.filePath}**?`)
            }
        };
    }
}

// Tool definitions for the LLM
const THIELE_TOOLS: vscode.LanguageModelChatTool[] = [
    {
        name: 'thiele_workspace_structure',
        description: 'Get the workspace directory structure to understand where files are organized. Returns a tree of folders and files.',
        inputSchema: {
            type: 'object',
            properties: {
                path: {
                    type: 'string',
                    description: 'Optional relative path to start from. Leave empty for workspace root.'
                }
            }
        }
    },
    {
        name: 'thiele_find_similar',
        description: 'Find similar files by name pattern and extension to determine where this type of file belongs.',
        inputSchema: {
            type: 'object',
            properties: {
                pattern: {
                    type: 'string',
                    description: 'Text pattern to search for in filenames (e.g., "test", "util", "helper")'
                },
                extension: {
                    type: 'string',
                    description: 'File extension including dot (e.g., ".py", ".ts", ".js")'
                }
            },
            required: ['pattern', 'extension']
        }
    },
    {
        name: 'thiele_create_file',
        description: 'Create a file at the specified path with the given content.',
        inputSchema: {
            type: 'object',
            properties: {
                filePath: {
                    type: 'string',
                    description: 'Relative path from workspace root where the file should be created'
                },
                content: {
                    type: 'string',
                    description: 'The content to write to the file'
                }
            },
            required: ['filePath', 'content']
        }
    }
];

// Tool instances
const toolInstances: Record<string, vscode.LanguageModelTool<any>> = {
    'thiele_workspace_structure': new WorkspaceStructureTool(),
    'thiele_find_similar': new FindSimilarFilesTool(),
    'thiele_create_file': new CreateFileTool()
};

export async function activate(context: vscode.ExtensionContext) {
    outputChannel = vscode.window.createOutputChannel('Thiele Verifier');
    outputChannel.show();
    outputChannel.appendLine('🛡️ Thiele Enforced Chat v3.0 - Agentic File Placement via MCP Tools');

    // Initialize verifier client
    verifierClient = new ThieleVerifierClient('http://localhost:7331');

    // Register MCP-style tools
    context.subscriptions.push(
        vscode.lm.registerTool('thiele_workspace_structure', new WorkspaceStructureTool()),
        vscode.lm.registerTool('thiele_find_similar', new FindSimilarFilesTool()),
        vscode.lm.registerTool('thiele_create_file', new CreateFileTool())
    );
    outputChannel.appendLine('🔧 Registered 3 agentic tools: workspace_structure, find_similar, create_file');

    // Chat participant
    const participant = vscode.chat.createChatParticipant(
        'thiele.enforced',
        handleChat
    );
    participant.iconPath = vscode.Uri.joinPath(context.extensionUri, 'icon.svg');
    context.subscriptions.push(participant);

    // Right-click commands
    context.subscriptions.push(
        vscode.commands.registerCommand('thiele.verifySelection', verifySelection),
        vscode.commands.registerCommand('thiele.fixSelection', fixSelection),
        vscode.commands.registerCommand('thiele.verifyFile', verifyFile),
        vscode.commands.registerCommand('thiele.showStats', showStats)
    );

    // Status bar
    const statusBar = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right, 100);
    statusBar.text = '$(shield) Thiele';
    statusBar.tooltip = 'Thiele Verifier Active - Agentic Mode';
    statusBar.show();
    context.subscriptions.push(statusBar);
}

async function handleChat(
    request: vscode.ChatRequest,
    context: vscode.ChatContext,
    stream: vscode.ChatResponseStream,
    token: vscode.CancellationToken
): Promise<vscode.ChatResult> {
    
    outputChannel.appendLine(`\n${'='.repeat(60)}`);
    outputChannel.appendLine(`Request: ${request.prompt}`);
    outputChannel.appendLine(`Command: ${request.command || 'none'}`);
    outputChannel.appendLine(`Tool refs: ${request.toolReferences?.length || 0}`);
    
    // Handle slash commands
    if (request.command === 'stats') {
        return await handleStatsCommand(stream);
    }
    if (request.command === 'verify') {
        return await handleVerifyCommand(request.prompt, stream);
    }
    if (request.command === 'synthesize') {
        return await handleSynthesizeCommand(request.prompt, request.model, stream, token);
    }
    
    // Step 1: Get model
    const model = request.model;
    outputChannel.appendLine(`Model from request: ${model ? model.id : 'NONE'}`);
    
    if (!model) {
        stream.markdown('❌ **No model available**\n');
        return { metadata: { error: 'no_model' } };
    }

    stream.markdown('# 🛡️ Thiele Verified Generation\n\n');
    stream.markdown(`**Model:** \`${model.id}\` | **Mode:** Agentic MCP\n\n`);
    stream.markdown('---\n\n');

    try {
        // ═══════════════════════════════════════════════════════════════
        // PHASE 1: Generate code with streaming
        // ═══════════════════════════════════════════════════════════════
        stream.progress('Generating code...');
        
        const codeGenMessages = [
            vscode.LanguageModelChatMessage.User(request.prompt)
        ];

        const chatResponse = await model.sendRequest(codeGenMessages, {}, token);

        let fullResponse = '';
        let chunkCount = 0;
        let streamStarted = false;

        for await (const chunk of chatResponse.text) {
            if (token.isCancellationRequested) {
                stream.markdown('\n\n*Cancelled*\n');
                return { metadata: { cancelled: true } };
            }
            
            fullResponse += chunk;
            chunkCount++;
            
            if (!streamStarted && fullResponse.length > 50) {
                stream.markdown('## 📝 Code Generation (Live)\n\n');
                streamStarted = true;
            }
            
            if (streamStarted) {
                stream.markdown(chunk);
            }
        }

        if (!streamStarted) {
            stream.markdown('## 📝 Response\n\n');
            stream.markdown(fullResponse);
        }

        outputChannel.appendLine(`Complete: ${chunkCount} chunks, ${fullResponse.length} chars`);

        // ═══════════════════════════════════════════════════════════════
        // PHASE 2: Verification
        // ═══════════════════════════════════════════════════════════════
        const codeBlocks = extractCodeBlocks(fullResponse);
        outputChannel.appendLine(`Found ${codeBlocks.length} code blocks`);

        if (codeBlocks.length === 0) {
            return { metadata: { verified: true, codeBlocks: 0 } };
        }

        stream.markdown('\n\n---\n\n## 🔬 Verification\n\n');
        stream.progress('Verifying code...');

        let verified = 0, blocked = 0;
        const verifiedBlocks: { code: string; lang: string }[] = [];
        const organicResults: OrganicVerificationResult[] = [];

        for (let i = 0; i < codeBlocks.length; i++) {
            const block = codeBlocks[i];
            
            if (shouldSkipLanguage(block.lang)) {
                stream.markdown(`**Block ${i + 1}** (${block.lang}): ⏭️ Skipped\n`);
                continue;
            }

            if (block.lang === 'python' || block.lang === 'py' || block.lang === '') {
                stream.progress(`Verifying block ${i + 1}...`);
                const organic = await verifierClient.verifyOrganic(request.prompt, block.code);
                organicResults.push(organic);
                
                if (organic.testsRun > 0) {
                    stream.markdown(`**Block ${i + 1}:** ${organic.explanation}\n`);
                    
                    if (organic.testResults.length > 0) {
                        stream.markdown('\n| Input | Expected | Actual | |\n');
                        stream.markdown('|-------|----------|--------|--|\n');
                        for (const tr of organic.testResults) {
                            const icon = tr.passed ? '✅' : '❌';
                            stream.markdown(`| \`${JSON.stringify(tr.inputs).slice(0, 25)}\` | \`${tr.expected}\` | \`${tr.actual}\` | ${icon} |\n`);
                        }
                        stream.markdown('\n');
                    }
                    
                    if (organic.success) {
                        verified++;
                        verifiedBlocks.push({ code: block.code, lang: block.lang || 'python' });
                    } else {
                        blocked++;
                    }
                } else {
                    const result = await verifierClient.verify(block.code, block.lang);
                    if (result.valid) {
                        verified++;
                        verifiedBlocks.push({ code: block.code, lang: block.lang || 'python' });
                        stream.markdown(`**Block ${i + 1}:** ✅ Syntax valid\n`);
                    } else {
                        blocked++;
                        stream.markdown(`**Block ${i + 1}:** ❌ ${result.error}\n`);
                    }
                }
            } else {
                const result = await verifierClient.verify(block.code, block.lang);
                if (result.valid) {
                    verified++;
                    verifiedBlocks.push({ code: block.code, lang: block.lang });
                    stream.markdown(`**Block ${i + 1}** (${block.lang}): ✅ Syntax valid\n`);
                } else {
                    blocked++;
                    stream.markdown(`**Block ${i + 1}** (${block.lang}): ❌ ${result.error}\n`);
                }
            }
        }

        const testsRun = organicResults.reduce((sum, r) => sum + r.testsRun, 0);
        const testsPassed = organicResults.reduce((sum, r) => sum + r.testsPassed, 0);
        
        stream.markdown(`\n**Summary:** ${verified} ✅ verified, ${blocked} ⚠️ issues`);
        if (testsRun > 0) {
            stream.markdown(` | ${testsPassed}/${testsRun} tests passed`);
        }
        stream.markdown('\n');

        // ═══════════════════════════════════════════════════════════════
        // PHASE 3: AGENTIC FILE PLACEMENT via MCP Tools
        // The LLM decides where files should go based on workspace context
        // ═══════════════════════════════════════════════════════════════
        if (verifiedBlocks.length > 0 && blocked === 0) {
            stream.markdown('\n---\n\n## 🧠 Agentic File Placement\n\n');
            stream.progress('Analyzing workspace structure...');

            const wsFolder = vscode.workspace.workspaceFolders?.[0];
            if (!wsFolder) {
                stream.markdown('⚠️ No workspace folder open\n');
                return { metadata: { success: true, verifiedCount: verified, noWorkspace: true } };
            }

            // Build agentic prompt for file placement
            for (let i = 0; i < verifiedBlocks.length; i++) {
                const block = verifiedBlocks[i];
                const ext = getExtensionForLang(block.lang);
                
                stream.markdown(`\n### Block ${i + 1} (${block.lang})\n`);
                stream.progress('Agent analyzing placement...');

                // Use tool-calling to determine file placement
                const placementResult = await determineFilePlacement(
                    model,
                    request.prompt,
                    block.code,
                    block.lang,
                    ext,
                    request.toolInvocationToken,
                    token
                );

                outputChannel.appendLine(`Placement result: ${JSON.stringify(placementResult)}`);

                if (placementResult.filePath) {
                    // Create the file at the agent-determined location
                    const absolutePath = path.isAbsolute(placementResult.filePath)
                        ? placementResult.filePath
                        : path.join(wsFolder.uri.fsPath, placementResult.filePath);

                    try {
                        const dir = path.dirname(absolutePath);
                        if (!fs.existsSync(dir)) {
                            fs.mkdirSync(dir, { recursive: true });
                        }
                        
                        fs.writeFileSync(absolutePath, block.code);
                        
                        const fileUri = vscode.Uri.file(absolutePath);
                        
                        stream.markdown(`📍 **Reasoning:** ${placementResult.reasoning}\n\n`);
                        stream.markdown(`✅ Created: `);
                        stream.anchor(fileUri, placementResult.filePath);
                        stream.markdown(`\n`);
                        
                        const doc = await vscode.workspace.openTextDocument(fileUri);
                        await vscode.window.showTextDocument(doc, { 
                            preview: false, 
                            viewColumn: vscode.ViewColumn.Beside 
                        });
                        
                        outputChannel.appendLine(`Created file: ${absolutePath}`);
                    } catch (err: any) {
                        stream.markdown(`❌ Failed to create: ${err.message}\n`);
                        outputChannel.appendLine(`Error: ${err}`);
                    }
                } else {
                    stream.markdown(`⚠️ Agent could not determine placement: ${placementResult.reasoning}\n`);
                }
            }
        } else if (blocked > 0) {
            stream.markdown('\n⚠️ **Not saving** - verification failed\n');
        }

        return { metadata: { success: blocked === 0, verifiedCount: verified, blockedCount: blocked, testsRun, testsPassed } };

    } catch (error: any) {
        outputChannel.appendLine(`ERROR: ${error}`);
        stream.markdown(`\n\n❌ **Error:** ${error.message || error}\n`);
        return { metadata: { error: String(error) } };
    }
}

/**
 * 🧠 AGENTIC FILE PLACEMENT
 * Uses LLM with tools to determine where a file should be placed
 */
async function determineFilePlacement(
    model: vscode.LanguageModelChat,
    userPrompt: string,
    code: string,
    lang: string,
    ext: string,
    toolToken: vscode.ChatParticipantToolToken | undefined,
    cancellation: vscode.CancellationToken
): Promise<{ filePath: string | null; reasoning: string }> {
    
    const wsFolder = vscode.workspace.workspaceFolders?.[0];
    if (!wsFolder) {
        return { filePath: null, reasoning: 'No workspace folder' };
    }

    // Build a prompt that instructs the LLM to use tools
    const placementPrompt = `You are an intelligent file placement agent. Your task is to determine the BEST location for a new file in the workspace.

USER REQUEST: "${userPrompt}"

CODE TO PLACE (${lang}):
\`\`\`${lang}
${code}
\`\`\`

INSTRUCTIONS:
1. First, use thiele_workspace_structure to understand the project layout
2. Then, use thiele_find_similar to find where similar files are located
3. Based on your analysis, determine the BEST path for this file

RULES FOR PLACEMENT:
- If it's a TEST file (contains "test_" or "_test" or "Test"), place in tests/ directory
- If it's a UTILITY/HELPER, place in src/ or utils/ or lib/
- If it's a SCRIPT, place in scripts/
- If it's a CONFIG file, place in configs/
- If it's an EXAMPLE, place in examples/
- If it's related to existing modules, place near them
- Generate an appropriate filename based on the code content

Return ONLY a JSON object with:
{
  "filePath": "relative/path/to/file${ext}",
  "reasoning": "Brief explanation of why this location was chosen"
}`;

    try {
        // Send request WITH tools enabled
        const messages = [vscode.LanguageModelChatMessage.User(placementPrompt)];
        
        const response = await model.sendRequest(messages, { 
            tools: THIELE_TOOLS 
        }, cancellation);

        // Process response - handle tool calls
        let textContent = '';
        const toolCalls: any[] = [];

        for await (const part of response.stream) {
            if (part instanceof vscode.LanguageModelTextPart) {
                textContent += part.value;
            } else if (part instanceof vscode.LanguageModelToolCallPart) {
                toolCalls.push(part);
                outputChannel.appendLine(`Tool call: ${part.name} with ${JSON.stringify(part.input)}`);
                
                // Execute the tool
                const toolInstance = toolInstances[part.name];
                if (toolInstance) {
                    const toolResult = await toolInstance.invoke({
                        input: part.input,
                        toolInvocationToken: toolToken
                    }, cancellation);
                    
                    // For multi-turn: we'd need to send tool results back
                    // For now, continue with available info
                    outputChannel.appendLine(`Tool result: ${toolResult}`);
                }
            }
        }

        // If we got tool calls, do a follow-up to get final answer
        if (toolCalls.length > 0) {
            // Execute tools and collect results
            const toolResults: string[] = [];
            for (const tc of toolCalls) {
                const toolInstance = toolInstances[tc.name];
                if (toolInstance) {
                    const result = await toolInstance.invoke({
                        input: tc.input,
                        toolInvocationToken: toolToken
                    }, cancellation);
                    
                    // Extract text from result
                    if (result && result.content) {
                        const resultText = result.content
                            .filter((p: any) => p instanceof vscode.LanguageModelTextPart)
                            .map((p: any) => p.value)
                            .join('\n');
                        toolResults.push(`${tc.name}: ${resultText}`);
                    }
                }
            }

            // Send follow-up with tool results
            const followUpMessages = [
                vscode.LanguageModelChatMessage.User(placementPrompt),
                vscode.LanguageModelChatMessage.Assistant(toolCalls.map(tc => 
                    `I'll call ${tc.name}(${JSON.stringify(tc.input)})`
                ).join('\n')),
                vscode.LanguageModelChatMessage.User(`Tool results:\n${toolResults.join('\n')}\n\nNow provide the final JSON with filePath and reasoning.`)
            ];

            const followUp = await model.sendRequest(followUpMessages, {}, cancellation);
            textContent = '';
            for await (const chunk of followUp.text) {
                textContent += chunk;
            }
        }

        // Parse JSON from response
        const jsonMatch = textContent.match(/\{[\s\S]*?"filePath"[\s\S]*?"reasoning"[\s\S]*?\}/);
        if (jsonMatch) {
            try {
                const parsed = JSON.parse(jsonMatch[0]);
                return {
                    filePath: parsed.filePath || null,
                    reasoning: parsed.reasoning || 'Agent determined placement'
                };
            } catch {
                // Fallback parsing
            }
        }

        // Fallback: generate smart default
        return generateSmartDefault(userPrompt, code, lang, ext);

    } catch (error: any) {
        outputChannel.appendLine(`Agent error: ${error}`);
        return generateSmartDefault(userPrompt, code, lang, ext);
    }
}

/**
 * Generate a smart default placement when agent fails
 */
function generateSmartDefault(
    prompt: string,
    code: string,
    lang: string,
    ext: string
): { filePath: string; reasoning: string } {
    const promptLower = prompt.toLowerCase();
    const codeLower = code.toLowerCase();
    
    // Detect file type from content
    const isTest = codeLower.includes('def test_') || 
                   codeLower.includes('class test') ||
                   promptLower.includes('test') ||
                   promptLower.includes('unittest');
    
    const isUtil = promptLower.includes('util') || 
                   promptLower.includes('helper') ||
                   promptLower.includes('tool');
    
    const isScript = promptLower.includes('script') ||
                     codeLower.includes('if __name__');
    
    const isExample = promptLower.includes('example') ||
                      promptLower.includes('demo');

    // Generate filename
    const words = prompt.toLowerCase()
        .replace(/[^a-z0-9\s]/g, '')
        .split(/\s+/)
        .filter(w => w.length > 2 && !['the', 'and', 'for', 'that', 'this', 'with', 'create', 'write', 'make', 'function', 'class', 'python'].includes(w))
        .slice(0, 3);
    
    let filename = words.length > 0 
        ? words.join('_') + ext
        : `generated_${Date.now().toString(36)}${ext}`;

    // Determine directory
    let dir: string;
    let reasoning: string;
    
    if (isTest) {
        dir = 'tests';
        filename = filename.startsWith('test_') ? filename : `test_${filename}`;
        reasoning = 'Detected test code, placing in tests/ directory';
    } else if (isUtil) {
        dir = 'src';
        reasoning = 'Detected utility code, placing in src/ directory';
    } else if (isScript) {
        dir = 'scripts';
        reasoning = 'Detected standalone script, placing in scripts/ directory';
    } else if (isExample) {
        dir = 'examples';
        reasoning = 'Detected example code, placing in examples/ directory';
    } else {
        dir = 'src';
        reasoning = 'Default placement in src/ directory';
    }

    return {
        filePath: `${dir}/${filename}`,
        reasoning
    };
}

/**
 * Get file extension for language
 */
function getExtensionForLang(lang: string): string {
    const map: { [key: string]: string } = {
        'python': '.py', 'py': '.py',
        'javascript': '.js', 'js': '.js',
        'typescript': '.ts', 'ts': '.ts',
        'java': '.java',
        'cpp': '.cpp', 'c++': '.cpp',
        'c': '.c',
        'go': '.go',
        'rust': '.rs',
        'ruby': '.rb',
        'php': '.php',
        'swift': '.swift',
        'kotlin': '.kt',
    };
    return map[lang.toLowerCase()] || '.txt';
}

// Helper function for backward compatibility
async function verifyCode(code: string, lang: string): Promise<{ valid: boolean; error?: string }> {
    return verifierClient.verify(code, lang);
}

// Right-click commands
async function verifySelection() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) return;
    
    const code = editor.document.getText(editor.selection);
    const lang = editor.document.languageId;
    
    if (!code.trim()) {
        vscode.window.showWarningMessage('No code selected');
        return;
    }
    
    const result = await verifyCode(code, lang);
    
    if (result.valid) {
        vscode.window.showInformationMessage(`✅ Code verified! (${lang})`);
    } else {
        vscode.window.showErrorMessage(`⛔ Error: ${result.error}`);
    }
}

async function fixSelection() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) return;
    
    const code = editor.document.getText(editor.selection);
    const lang = editor.document.languageId;
    
    vscode.commands.executeCommand('workbench.action.chat.open', {
        query: `@thiele Fix this ${lang} code:\n\`\`\`${lang}\n${code}\n\`\`\``
    });
}

async function verifyFile() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) return;
    
    const code = editor.document.getText();
    const lang = editor.document.languageId;
    const name = editor.document.fileName.split('/').pop();
    
    const result = await verifyCode(code, lang);
    
    if (result.valid) {
        vscode.window.showInformationMessage(`✅ ${name} verified!`);
    } else {
        vscode.window.showErrorMessage(`⛔ ${name}: ${result.error}`);
    }
}

// Slash command handlers
async function handleStatsCommand(stream: vscode.ChatResponseStream): Promise<vscode.ChatResult> {
    stream.markdown('# 📊 Thiele Verification Statistics\n\n');
    
    try {
        const data = await verifierClient.getStatus();
        
        stream.markdown('## Server Status\n\n');
        stream.markdown(`- **Status:** ${data.status}\n`);
        stream.markdown(`- **Uptime:** ${Math.round(data.statistics.uptime_sec / 60)} minutes\n\n`);
        
        stream.markdown('## Verification Stats\n\n');
        stream.markdown(`| Metric | Value |\n`);
        stream.markdown(`|--------|-------|\n`);
        stream.markdown(`| Total Verifications | ${data.statistics.total_verifications} |\n`);
        stream.markdown(`| Verified ✅ | ${data.statistics.verified} |\n`);
        stream.markdown(`| Failed ⛔ | ${data.statistics.failed} |\n`);
        stream.markdown(`| Success Rate | ${(data.statistics.verification_rate * 100).toFixed(1)}% |\n`);
        stream.markdown(`| μ-Cost Consumed | ${data.statistics.mu_consumed} |\n`);
        stream.markdown(`| μ-Budget Remaining | ${data.statistics.mu_remaining} |\n`);
        
        return { metadata: { command: 'stats', success: true } };
    } catch (e) {
        stream.markdown('❌ **Error:** Could not connect to verification server.\n\n');
        stream.markdown('Make sure the Thiele verification server is running on port 7331.\n');
        return { metadata: { command: 'stats', error: String(e) } };
    }
}

async function handleVerifyCommand(code: string, stream: vscode.ChatResponseStream): Promise<vscode.ChatResult> {
    stream.markdown('# 🔬 Direct Verification\n\n');
    
    if (!code.trim()) {
        stream.markdown('Please provide code to verify. Example:\n\n');
        stream.markdown('```\n@thiele /verify def hello(): print("world")\n```\n');
        return { metadata: { command: 'verify', error: 'no_code' } };
    }
    
    // Auto-detect language using imported function
    const lang = detectLanguage(code);
    
    stream.markdown(`**Detected language:** ${lang}\n\n`);
    
    const result = await verifierClient.verify(code, lang);
    
    if (result.valid) {
        stream.markdown('✅ **Code is valid!**\n\n');
        stream.markdown('```' + lang + '\n' + code + '\n```\n');
    } else {
        stream.markdown(`⛔ **Verification failed:** ${result.error}\n\n`);
        stream.markdown('```\n' + code + '\n```\n');
    }
    
    return { metadata: { command: 'verify', valid: result.valid } };
}

async function showStats() {
    try {
        const data = await verifierClient.getStatus();
        
        const message = `Thiele Stats: ${data.statistics.verified}/${data.statistics.total_verifications} verified (${(data.statistics.verification_rate * 100).toFixed(1)}%)`;
        vscode.window.showInformationMessage(message);
    } catch (e) {
        vscode.window.showErrorMessage('Could not connect to verification server');
    }
}

/**
 * 🚀 GROUNDBREAKING: Self-Correcting Verified Code Synthesis
 * 
 * This is where the magic happens:
 * 1. Parse user's specification from prompt
 * 2. LLM generates code
 * 3. Thiele server EXECUTES code against test cases
 * 4. If tests fail, automatically send failures back to LLM
 * 5. Loop until ALL tests pass
 * 6. Generate cryptographic receipt
 */
async function handleSynthesizeCommand(
    prompt: string,
    model: vscode.LanguageModelChat | undefined,
    stream: vscode.ChatResponseStream,
    token: vscode.CancellationToken
): Promise<vscode.ChatResult> {
    stream.markdown('# 🚀 Verified Code Synthesis\n\n');
    stream.markdown('> **GROUNDBREAKING:** Self-correcting code generation with execution verification\n\n');
    
    if (!prompt.trim()) {
        stream.markdown('## Usage\n\n');
        stream.markdown('Provide a specification with test cases:\n\n');
        stream.markdown('```\n');
        stream.markdown('@thiele /synthesize\n');
        stream.markdown('Function: fibonacci(n: int) -> int\n');
        stream.markdown('Description: Return the nth Fibonacci number\n');
        stream.markdown('Tests:\n');
        stream.markdown('  fibonacci(0) = 0\n');
        stream.markdown('  fibonacci(1) = 1\n');
        stream.markdown('  fibonacci(10) = 55\n');
        stream.markdown('```\n\n');
        stream.markdown('The system will:\n');
        stream.markdown('1. Generate code using the LLM\n');
        stream.markdown('2. **Execute** it against ALL test cases\n');
        stream.markdown('3. Auto-correct until all tests pass\n');
        stream.markdown('4. Provide cryptographic receipt\n');
        return { metadata: { command: 'synthesize', error: 'no_spec' } };
    }
    
    if (!model) {
        stream.markdown('❌ **Error:** No LLM model available\n');
        return { metadata: { command: 'synthesize', error: 'no_model' } };
    }
    
    // Parse specification from prompt
    const spec = parseSpecification(prompt);
    if (!spec) {
        stream.markdown('❌ **Error:** Could not parse specification\n\n');
        stream.markdown('Make sure to include:\n');
        stream.markdown('- Function signature\n');
        stream.markdown('- At least one test case like `func(args) = expected`\n');
        return { metadata: { command: 'synthesize', error: 'parse_error' } };
    }
    
    stream.markdown('## 📋 Specification Parsed\n\n');
    stream.markdown(`**Function:** \`${spec.signature}\`\n\n`);
    stream.markdown('**Test Cases:**\n');
    for (const tc of spec.testCases) {
        stream.markdown(`- \`${tc.call}\` → \`${JSON.stringify(tc.expected)}\`\n`);
    }
    stream.markdown('\n---\n\n');
    
    const maxIterations = 5;
    let finalCode: string | null = null;
    let iterations = 0;
    let currentPrompt = buildSynthesisPrompt(spec);
    
    for (let i = 1; i <= maxIterations; i++) {
        if (token.isCancellationRequested) {
            stream.markdown('\n*Cancelled*\n');
            return { metadata: { command: 'synthesize', cancelled: true } };
        }
        
        iterations = i;
        stream.markdown(`## 🔄 Iteration ${i}/${maxIterations}\n\n`);
        
        // Get code from LLM
        stream.markdown('📡 Generating code...\n\n');
        
        const messages = [vscode.LanguageModelChatMessage.User(currentPrompt)];
        const response = await model.sendRequest(messages, {}, token);
        
        let llmResponse = '';
        for await (const chunk of response.text) {
            llmResponse += chunk;
        }
        
        // Extract code
        const code = extractCodeFromResponse(llmResponse);
        stream.markdown('```python\n' + code + '\n```\n\n');
        
        // Execute against test cases via server
        stream.markdown('🧪 **Executing test cases...**\n\n');
        
        const result = await executeTests(spec, code);
        
        stream.markdown('| Test | Input | Expected | Actual | Status |\n');
        stream.markdown('|------|-------|----------|--------|--------|\n');
        
        let allPassed = true;
        const failures: string[] = [];
        
        for (const tr of result.results) {
            const status = tr.passed ? '✅' : '❌';
            stream.markdown(`| ${tr.call} | ${tr.input} | ${tr.expected} | ${tr.actual} | ${status} |\n`);
            if (!tr.passed) {
                allPassed = false;
                failures.push(`${tr.call}: expected ${tr.expected}, got ${tr.actual}${tr.error ? ` (${tr.error})` : ''}`);
            }
        }
        
        stream.markdown('\n');
        
        if (allPassed) {
            stream.markdown('### 🎉 ALL TESTS PASSED!\n\n');
            finalCode = code;
            break;
        }
        
        stream.markdown(`### ❌ ${failures.length} test(s) failed\n\n`);
        
        if (i < maxIterations) {
            stream.markdown('🔧 Preparing correction prompt...\n\n---\n\n');
            currentPrompt = buildCorrectionPrompt(spec, code, failures);
        }
    }
    
    // Generate receipt
    stream.markdown('---\n\n## 📜 Synthesis Receipt\n\n');
    
    if (finalCode) {
        const codeHash = await hashString(finalCode);
        const specHash = await hashString(JSON.stringify(spec));
        const certHash = await hashString(`${specHash}:${codeHash}:${iterations}`);
        
        stream.markdown('✅ **SYNTHESIS SUCCESSFUL**\n\n');
        stream.markdown('### Final Verified Code\n\n');
        stream.markdown('```python\n' + finalCode + '\n```\n\n');
        stream.markdown('### Cryptographic Receipt\n\n');
        stream.markdown(`| Field | Value |\n`);
        stream.markdown(`|-------|-------|\n`);
        stream.markdown(`| Iterations | ${iterations} |\n`);
        stream.markdown(`| Spec Hash | \`${specHash.slice(0, 16)}...\` |\n`);
        stream.markdown(`| Code Hash | \`${codeHash.slice(0, 16)}...\` |\n`);
        stream.markdown(`| Certificate | \`${certHash.slice(0, 32)}...\` |\n`);
        
        return { metadata: { command: 'synthesize', success: true, iterations, certHash } };
    } else {
        stream.markdown('❌ **SYNTHESIS FAILED** after ' + maxIterations + ' iterations\n\n');
        stream.markdown('The LLM could not produce code that passes all test cases.\n');
        return { metadata: { command: 'synthesize', success: false, iterations } };
    }
}

// Helper types for synthesis
interface ParsedSpec {
    name: string;
    signature: string;
    description: string;
    testCases: { call: string; args: Record<string, any>; expected: any }[];
}

interface TestResult {
    call: string;
    input: string;
    expected: string;
    actual: string;
    passed: boolean;
    error?: string;
}

function parseSpecification(prompt: string): ParsedSpec | null {
    // Try to parse function signature
    const sigMatch = prompt.match(/(?:Function|def|Signature):\s*(\w+)\s*\(([^)]*)\)/i);
    if (!sigMatch) {
        // Try simpler pattern
        const simpleMatch = prompt.match(/(\w+)\s*\(([^)]*)\)/);
        if (!simpleMatch) return null;
    }
    
    const funcName = sigMatch ? sigMatch[1] : prompt.match(/(\w+)\s*\(/)?.[1] || 'solve';
    
    // Parse test cases: func(args) = expected or func(args) -> expected
    const testPattern = /(\w+)\s*\(([^)]*)\)\s*(?:=|→|->)+\s*([^\n,]+)/g;
    const testCases: ParsedSpec['testCases'] = [];
    
    let match;
    while ((match = testPattern.exec(prompt)) !== null) {
        const call = `${match[1]}(${match[2]})`;
        const expected = parseValue(match[3].trim());
        
        // Parse args
        const argsStr = match[2];
        const args: Record<string, any> = {};
        
        // Handle positional args
        const argParts = argsStr.split(',').map(s => s.trim()).filter(Boolean);
        argParts.forEach((part, i) => {
            const value = parseValue(part);
            args[`arg${i}`] = value;
        });
        
        testCases.push({ call, args, expected });
    }
    
    if (testCases.length === 0) return null;
    
    // Extract description
    const descMatch = prompt.match(/(?:Description|Desc):\s*([^\n]+)/i);
    const description = descMatch ? descMatch[1].trim() : 'Implement the function';
    
    return {
        name: funcName,
        signature: `def ${funcName}(${sigMatch?.[2] || 'n'})`,
        description,
        testCases
    };
}

function parseValue(str: string): any {
    str = str.trim();
    // Try JSON parse
    try {
        return JSON.parse(str);
    } catch {
        // Try as number
        const num = Number(str);
        if (!isNaN(num)) return num;
        // Return as string
        return str;
    }
}

function buildSynthesisPrompt(spec: ParsedSpec): string {
    const tests = spec.testCases.map(tc => `  ${tc.call} = ${JSON.stringify(tc.expected)}`).join('\n');
    return `Write a Python function that satisfies this specification:

**Function:** ${spec.signature}
**Description:** ${spec.description}

**Test Cases (ALL must pass):**
${tests}

Return ONLY the function implementation. No explanations or markdown.`;
}

function buildCorrectionPrompt(spec: ParsedSpec, code: string, failures: string[]): string {
    return `Your previous code FAILED. Fix it.

**Specification:**
${spec.signature}
${spec.description}

**Your Previous Code:**
\`\`\`python
${code}
\`\`\`

**Failures:**
${failures.map(f => `- ${f}`).join('\n')}

Analyze the failures and provide a CORRECTED implementation.
Return ONLY the fixed function. No explanations.`;
}

function extractCodeFromResponse(response: string): string {
    // Try to find code block
    const match = response.match(/```(?:python)?\n([\s\S]*?)```/);
    if (match) return match[1].trim();
    // Otherwise return as-is
    return response.trim();
}

async function executeTests(spec: ParsedSpec, code: string): Promise<{ results: TestResult[] }> {
    // Build execution payload
    const testCases = spec.testCases.map(tc => ({
        call: tc.call,
        args: tc.args,
        expected: tc.expected
    }));
    
    try {
        const resp = await fetch('http://localhost:7331/synthesize/execute', {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({
                code,
                function_name: spec.name,
                test_cases: testCases
            })
        });
        
        const data = await resp.json() as any;
        return {
            results: data.results || testCases.map(tc => ({
                call: tc.call,
                input: JSON.stringify(tc.args),
                expected: JSON.stringify(tc.expected),
                actual: 'ERROR',
                passed: false,
                error: 'Server error'
            }))
        };
    } catch (e) {
        // Fallback: execute locally via verify endpoint (syntax only)
        return {
            results: testCases.map(tc => ({
                call: tc.call,
                input: JSON.stringify(tc.args),
                expected: JSON.stringify(tc.expected),
                actual: 'CANNOT_EXECUTE',
                passed: false,
                error: 'Synthesis server endpoint not available'
            }))
        };
    }
}

async function hashString(str: string): Promise<string> {
    const encoder = new TextEncoder();
    const data = encoder.encode(str);
    const hashBuffer = await crypto.subtle.digest('SHA-256', data);
    const hashArray = Array.from(new Uint8Array(hashBuffer));
    return hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
}

export function deactivate() {}
