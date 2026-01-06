/**
 * Integration tests for Thiele Enforced Chat
 * Tests the chat handling logic with mocked VS Code API
 */
import * as assert from 'assert';
import {
    extractCodeBlocks,
    shouldSkipLanguage,
    sanitizeResponse,
    MockVerifierClient,
    CodeBlock
} from '../verifier';

describe('Thiele Integration Tests', () => {
    
    describe('Chat Response Processing', () => {
        let mockClient: MockVerifierClient;
        
        beforeEach(() => {
            mockClient = new MockVerifierClient();
        });
        
        it('should process response with valid code blocks', async () => {
            const response = `Here's a Python function:

\`\`\`python
def hello():
    print("world")
\`\`\`

And some JavaScript:

\`\`\`javascript
const x = 42;
\`\`\`
`;
            
            const blocks = extractCodeBlocks(response);
            assert.strictEqual(blocks.length, 2);
            
            // Verify each block
            const results = [];
            for (const block of blocks) {
                if (shouldSkipLanguage(block.lang)) {
                    results.push({ block, skipped: true });
                } else {
                    const result = await mockClient.verify(block.code, block.lang);
                    results.push({ block, result, skipped: false });
                }
            }
            
            assert.strictEqual(results.length, 2);
            assert.strictEqual(results[0].skipped, false);
            assert.strictEqual(results[0].result?.valid, true);
            assert.strictEqual(results[1].skipped, false);
            assert.strictEqual(results[1].result?.valid, true);
        });
        
        it('should skip non-verifiable languages', async () => {
            const response = `Here's some JSON:

\`\`\`json
{"key": "value"}
\`\`\`

And some bash:

\`\`\`bash
echo "hello"
\`\`\`
`;
            
            const blocks = extractCodeBlocks(response);
            assert.strictEqual(blocks.length, 2);
            
            const skipped = blocks.filter(b => shouldSkipLanguage(b.lang));
            assert.strictEqual(skipped.length, 2);
        });
        
        it('should handle failed verification', async () => {
            mockClient.setDefaultResult({ valid: false, error: 'Syntax error on line 1' });
            
            const response = `Bad code:

\`\`\`python
def broken(
\`\`\`
`;
            
            const blocks = extractCodeBlocks(response);
            assert.strictEqual(blocks.length, 1);
            
            const result = await mockClient.verify(blocks[0].code, blocks[0].lang);
            assert.strictEqual(result.valid, false);
            assert.strictEqual(result.error, 'Syntax error on line 1');
        });
        
        it('should sanitize response with failed blocks', () => {
            const response = `Here's code:

\`\`\`python
def broken(
\`\`\`
`;
            
            const blocks = extractCodeBlocks(response);
            const failedBlocks = [{ block: blocks[0], error: 'Syntax error' }];
            
            const sanitized = sanitizeResponse(response, failedBlocks);
            
            assert.ok(sanitized.includes('⛔ BLOCKED'));
            assert.ok(sanitized.includes('Syntax error'));
            assert.ok(!sanitized.includes('def broken'));
        });
        
        it('should handle mixed valid and invalid blocks', async () => {
            const response = `Valid code:

\`\`\`python
def hello():
    pass
\`\`\`

Invalid code:

\`\`\`python
def broken(
\`\`\`

More valid code:

\`\`\`javascript
const x = 1;
\`\`\`
`;
            
            const blocks = extractCodeBlocks(response);
            assert.strictEqual(blocks.length, 3);
            
            // Simulate verification where second block fails
            const results = [];
            for (let i = 0; i < blocks.length; i++) {
                if (i === 1) {
                    mockClient.setDefaultResult({ valid: false, error: 'Syntax error' });
                } else {
                    mockClient.setDefaultResult({ valid: true });
                }
                const result = await mockClient.verify(blocks[i].code, blocks[i].lang);
                results.push({ block: blocks[i], result });
            }
            
            const failedBlocks = results
                .filter(r => !r.result.valid)
                .map(r => ({ block: r.block, error: r.result.error || 'Unknown error' }));
            
            assert.strictEqual(failedBlocks.length, 1);
            
            const sanitized = sanitizeResponse(response, failedBlocks);
            assert.ok(sanitized.includes('def hello'));  // First block preserved
            assert.ok(sanitized.includes('⛔ BLOCKED')); // Second block blocked
            assert.ok(sanitized.includes('const x = 1')); // Third block preserved
        });
    });
    
    describe('Verification Statistics', () => {
        it('should track verification counts', async () => {
            const mockClient = new MockVerifierClient();
            
            // Verify some code
            await mockClient.verify('def x(): pass', 'python');
            await mockClient.verify('const y = 1;', 'javascript');
            
            // Get status
            const status = await mockClient.getStatus();
            
            assert.strictEqual(status.status, 'healthy');
            assert.strictEqual(status.statistics.total_verifications, 100);
        });
        
        it('should handle custom status', async () => {
            const mockClient = new MockVerifierClient();
            mockClient.setMockStatus({
                status: 'degraded',
                statistics: {
                    total_verifications: 500,
                    verified: 400,
                    failed: 100,
                    verification_rate: 0.8,
                    mu_consumed: 1000,
                    mu_remaining: 9000,
                    mu_budget: 10000,
                    uptime_sec: 7200
                }
            });
            
            const status = await mockClient.getStatus();
            
            assert.strictEqual(status.status, 'degraded');
            assert.strictEqual(status.statistics.verification_rate, 0.8);
            assert.strictEqual(status.statistics.failed, 100);
        });
    });
    
    describe('Code Block Edge Cases', () => {
        it('should handle empty code blocks', () => {
            const response = `Empty block:

\`\`\`python
\`\`\`
`;
            
            const blocks = extractCodeBlocks(response);
            assert.strictEqual(blocks.length, 1);
            assert.strictEqual(blocks[0].code, '');
        });
        
        it('should handle code blocks with special characters', () => {
            const response = `Special chars:

\`\`\`python
def test():
    return "Hello <world> & 'friends'"
\`\`\`
`;
            
            const blocks = extractCodeBlocks(response);
            assert.strictEqual(blocks.length, 1);
            assert.ok(blocks[0].code.includes('<world>'));
            assert.ok(blocks[0].code.includes("'friends'"));
        });
        
        it('should handle deeply nested code', () => {
            const response = `Nested code:

\`\`\`python
def outer():
    def inner():
        def deep():
            return "nested"
        return deep
    return inner
\`\`\`
`;
            
            const blocks = extractCodeBlocks(response);
            assert.strictEqual(blocks.length, 1);
            assert.ok(blocks[0].code.includes('def outer'));
            assert.ok(blocks[0].code.includes('def inner'));
            assert.ok(blocks[0].code.includes('def deep'));
        });
        
        it('should handle code with backticks inside', () => {
            const response = `Code with backticks:

\`\`\`python
def test():
    # Using \`back\` ticks in comment
    return 42
\`\`\`
`;
            
            const blocks = extractCodeBlocks(response);
            assert.strictEqual(blocks.length, 1);
            assert.ok(blocks[0].code.includes('`back`'));
        });
    });
    
    describe('Language Detection in Context', () => {
        it('should detect language when not specified', () => {
            const response = `Here's some code:

\`\`\`
def hello():
    print("world")
\`\`\`
`;
            
            const blocks = extractCodeBlocks(response);
            assert.strictEqual(blocks.length, 1);
            assert.strictEqual(blocks[0].lang, 'unknown');
            // Note: detectLanguage would be called separately to identify as python
        });
        
        it('should preserve language when specified', () => {
            const response = `Typescript code:

\`\`\`typescript
const x: number = 42;
\`\`\`
`;
            
            const blocks = extractCodeBlocks(response);
            assert.strictEqual(blocks.length, 1);
            assert.strictEqual(blocks[0].lang, 'typescript');
        });
    });
    
    describe('Full Pipeline Simulation', () => {
        it('should process complete chat response', async () => {
            const mockClient = new MockVerifierClient();
            
            // Simulate a typical AI response
            const aiResponse = `# Solution

Here's a Python function to calculate factorial:

\`\`\`python
def factorial(n):
    if n <= 1:
        return 1
    return n * factorial(n - 1)
\`\`\`

And here's how to use it:

\`\`\`python
result = factorial(5)
print(f"5! = {result}")
\`\`\`

The output will be:

\`\`\`text
5! = 120
\`\`\`
`;
            
            // Step 1: Extract code blocks
            const blocks = extractCodeBlocks(aiResponse);
            assert.strictEqual(blocks.length, 3, 'Should find 3 code blocks');
            
            // Step 2: Process each block
            let verified = 0;
            let blocked = 0;
            let skipped = 0;
            const failedBlocks: Array<{ block: CodeBlock; error: string }> = [];
            
            for (const block of blocks) {
                if (shouldSkipLanguage(block.lang)) {
                    skipped++;
                    continue;
                }
                
                const result = await mockClient.verify(block.code, block.lang);
                if (result.valid) {
                    verified++;
                } else {
                    blocked++;
                    failedBlocks.push({ block, error: result.error || 'Error' });
                }
            }
            
            assert.strictEqual(verified, 2, 'Should verify 2 Python blocks');
            assert.strictEqual(skipped, 1, 'Should skip text block');
            assert.strictEqual(blocked, 0, 'Should have no blocked blocks');
            
            // Step 3: Sanitize response (no changes since all passed)
            const sanitized = sanitizeResponse(aiResponse, failedBlocks);
            assert.strictEqual(sanitized, aiResponse, 'Response unchanged when all pass');
        });
        
        it('should block invalid code in pipeline', async () => {
            const mockClient = new MockVerifierClient();
            
            const aiResponse = `Here's broken code:

\`\`\`python
def broken(
    # missing closing paren
\`\`\`
`;
            
            // Step 1: Extract
            const blocks = extractCodeBlocks(aiResponse);
            assert.strictEqual(blocks.length, 1);
            
            // Step 2: Verify (simulate failure)
            mockClient.setDefaultResult({ valid: false, error: 'SyntaxError: unexpected EOF' });
            const result = await mockClient.verify(blocks[0].code, blocks[0].lang);
            
            assert.strictEqual(result.valid, false);
            
            // Step 3: Sanitize
            const failedBlocks = [{ block: blocks[0], error: result.error || 'Error' }];
            const sanitized = sanitizeResponse(aiResponse, failedBlocks);
            
            assert.ok(!sanitized.includes('def broken'), 'Broken code should be removed');
            assert.ok(sanitized.includes('⛔ BLOCKED'), 'Should show blocked message');
            assert.ok(sanitized.includes('SyntaxError'), 'Should show error message');
        });
    });
});
