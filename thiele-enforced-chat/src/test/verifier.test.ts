/**
 * Unit tests for Thiele Verifier - Pure functions
 */

import * as assert from 'assert';
import {
    extractCodeBlocks,
    detectLanguage,
    shouldSkipLanguage,
    sanitizeResponse,
    formatTableRow,
    MockVerifierClient,
    SKIP_LANGUAGES,
    VERIFIABLE_LANGUAGES
} from '../verifier';

describe('Thiele Verifier Unit Tests', () => {
    
    describe('extractCodeBlocks', () => {
        it('should extract single code block', () => {
            const text = 'Here is some code:\n```python\nprint("hello")\n```\n';
            const blocks = extractCodeBlocks(text);
            
            assert.strictEqual(blocks.length, 1);
            assert.strictEqual(blocks[0].lang, 'python');
            assert.strictEqual(blocks[0].code, 'print("hello")\n');
        });

        it('should extract multiple code blocks', () => {
            const text = '```python\nprint(1)\n```\n\nSome text\n\n```javascript\nconsole.log(2)\n```';
            const blocks = extractCodeBlocks(text);
            
            assert.strictEqual(blocks.length, 2);
            assert.strictEqual(blocks[0].lang, 'python');
            assert.strictEqual(blocks[1].lang, 'javascript');
        });

        it('should handle code block without language', () => {
            const text = '```\nsome code\n```';
            const blocks = extractCodeBlocks(text);
            
            assert.strictEqual(blocks.length, 1);
            assert.strictEqual(blocks[0].lang, 'unknown');
        });

        it('should return empty array for text without code blocks', () => {
            const text = 'Just some regular text without any code.';
            const blocks = extractCodeBlocks(text);
            
            assert.strictEqual(blocks.length, 0);
        });

        it('should preserve full match for replacement', () => {
            const text = '```python\nprint("test")\n```';
            const blocks = extractCodeBlocks(text);
            
            assert.strictEqual(blocks[0].full, text);
        });

        it('should handle multiline code', () => {
            const code = 'def hello():\n    print("world")\n    return 42\n';
            const text = '```python\n' + code + '```';
            const blocks = extractCodeBlocks(text);
            
            assert.strictEqual(blocks[0].code, code);
        });
    });

    describe('detectLanguage', () => {
        it('should detect Python', () => {
            assert.strictEqual(detectLanguage('def hello(): pass'), 'python');
            assert.strictEqual(detectLanguage('import os'), 'python');
        });

        it('should detect JavaScript', () => {
            assert.strictEqual(detectLanguage('function foo() {}'), 'javascript');
            assert.strictEqual(detectLanguage('const x = 1'), 'javascript');
            assert.strictEqual(detectLanguage('let y = 2'), 'javascript');
            assert.strictEqual(detectLanguage('() => {}'), 'javascript');
        });

        it('should detect Rust', () => {
            assert.strictEqual(detectLanguage('fn main() {}'), 'rust');
            assert.strictEqual(detectLanguage('let mut x = 5;'), 'rust');
            assert.strictEqual(detectLanguage('impl Foo for Bar {}'), 'rust');
        });

        it('should detect Go', () => {
            assert.strictEqual(detectLanguage('func main() {}'), 'go');
            assert.strictEqual(detectLanguage('package main'), 'go');
        });

        it('should detect Coq', () => {
            assert.strictEqual(detectLanguage('Theorem foo: True.'), 'coq');
            assert.strictEqual(detectLanguage('Lemma bar: False.'), 'coq');
            assert.strictEqual(detectLanguage('Proof. trivial. Qed.'), 'coq');
        });

        it('should return unknown for unrecognized code', () => {
            assert.strictEqual(detectLanguage('some random text'), 'unknown');
        });
    });

    describe('shouldSkipLanguage', () => {
        it('should skip non-code languages', () => {
            for (const lang of SKIP_LANGUAGES) {
                assert.strictEqual(shouldSkipLanguage(lang), true, `Should skip ${lang}`);
            }
        });

        it('should not skip verifiable languages', () => {
            for (const lang of VERIFIABLE_LANGUAGES) {
                assert.strictEqual(shouldSkipLanguage(lang), false, `Should not skip ${lang}`);
            }
        });

        it('should be case insensitive', () => {
            assert.strictEqual(shouldSkipLanguage('JSON'), true);
            assert.strictEqual(shouldSkipLanguage('Html'), true);
        });
    });

    describe('sanitizeResponse', () => {
        it('should replace failed code blocks', () => {
            const response = 'Here:\n```python\nbad code\n```\nDone.';
            const block = { full: '```python\nbad code\n```', lang: 'python', code: 'bad code\n' };
            const result = sanitizeResponse(response, [{ block, error: 'Syntax error' }]);
            
            assert.ok(result.includes('⛔ BLOCKED: Syntax error'));
            assert.ok(!result.includes('bad code'));
        });

        it('should handle multiple failed blocks', () => {
            const response = '```python\nbad1\n```\n\n```javascript\nbad2\n```';
            const blocks = [
                { block: { full: '```python\nbad1\n```', lang: 'python', code: 'bad1\n' }, error: 'Error 1' },
                { block: { full: '```javascript\nbad2\n```', lang: 'javascript', code: 'bad2\n' }, error: 'Error 2' }
            ];
            const result = sanitizeResponse(response, blocks);
            
            assert.ok(result.includes('⛔ BLOCKED: Error 1'));
            assert.ok(result.includes('⛔ BLOCKED: Error 2'));
        });

        it('should preserve valid blocks', () => {
            const response = '```python\ngood\n```\n\n```javascript\nbad\n```';
            const block = { full: '```javascript\nbad\n```', lang: 'javascript', code: 'bad\n' };
            const result = sanitizeResponse(response, [{ block, error: 'Error' }]);
            
            assert.ok(result.includes('```python\ngood\n```'));
        });
    });

    describe('formatTableRow', () => {
        it('should format pass row', () => {
            const row = formatTableRow(1, 'python', 'pass', 'Valid syntax');
            assert.strictEqual(row, '| 1 | python | ✅ Pass | Valid syntax |\n');
        });

        it('should format fail row', () => {
            const row = formatTableRow(2, 'javascript', 'fail', 'Missing semicolon');
            assert.strictEqual(row, '| 2 | javascript | ⛔ Fail | Missing semicolon |\n');
        });

        it('should format skip row', () => {
            const row = formatTableRow(3, 'json', 'skip', 'Not code');
            assert.strictEqual(row, '| 3 | json | ⏭️ Skip | Not code |\n');
        });
    });

    describe('MockVerifierClient', () => {
        let client: MockVerifierClient;

        beforeEach(() => {
            client = new MockVerifierClient();
        });

        it('should return valid by default', async () => {
            const result = await client.verify('print("hello")', 'python');
            assert.strictEqual(result.valid, true);
        });

        it('should return mock result when set', async () => {
            client.setMockResult('bad code', { valid: false, error: 'Syntax error' });
            
            const result = await client.verify('bad code', 'python');
            assert.strictEqual(result.valid, false);
            assert.strictEqual(result.error, 'Syntax error');
        });

        it('should return mock status', async () => {
            const status = await client.getStatus();
            
            assert.strictEqual(status.status, 'healthy');
            assert.strictEqual(status.statistics.verified, 94);
            assert.strictEqual(status.statistics.failed, 6);
        });

        it('should allow setting custom status', async () => {
            client.setMockStatus({
                status: 'running',
                statistics: {
                    total_verifications: 100,
                    verified: 95,
                    failed: 5,
                    verification_rate: 0.95,
                    mu_consumed: 100,
                    mu_remaining: 9900,
                    mu_budget: 10000,
                    uptime_sec: 7200
                }
            });
            
            const status = await client.getStatus();
            assert.strictEqual(status.statistics.verified, 95);
        });

        it('should use default result when set', async () => {
            client.setDefaultResult({ valid: false, error: 'Default failure' });
            
            const result = await client.verify('any code', 'python');
            assert.strictEqual(result.valid, false);
            assert.strictEqual(result.error, 'Default failure');
        });

        it('should prefer specific mock over default result', async () => {
            client.setDefaultResult({ valid: false, error: 'Default failure' });
            client.setMockResult('specific code', { valid: true });
            
            // Specific mock takes precedence
            const result1 = await client.verify('specific code', 'python');
            assert.strictEqual(result1.valid, true);
            
            // Other code uses default
            const result2 = await client.verify('other code', 'python');
            assert.strictEqual(result2.valid, false);
        });

        it('should clear default result', async () => {
            client.setDefaultResult({ valid: false, error: 'Failure' });
            client.clearDefaultResult();
            
            const result = await client.verify('any code', 'python');
            assert.strictEqual(result.valid, true); // Back to built-in default
        });
    });
});
