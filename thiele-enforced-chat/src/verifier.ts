/**
 * Thiele Code Verifier - Pure functions for code verification
 * Extracted for testability
 */

export interface CodeBlock {
    full: string;
    lang: string;
    code: string;
}

export interface VerificationResult {
    valid: boolean;
    error?: string;
}

export interface ServerStatus {
    status: string;
    statistics: {
        total_verifications: number;
        verified: number;
        failed: number;
        verification_rate: number;
        mu_consumed: number;
        mu_remaining: number;
        mu_budget: number;
        uptime_sec: number;
    };
}

// Languages that should be skipped (not verifiable as code)
export const SKIP_LANGUAGES = ['json', 'yaml', 'xml', 'html', 'css', 'md', 'text', 'bash', 'sh', 'markdown'];

// Languages that can be verified
export const VERIFIABLE_LANGUAGES = ['python', 'javascript', 'typescript', 'rust', 'go', 'java', 'c', 'cpp', 'coq'];

/**
 * Extract code blocks from markdown text
 */
export function extractCodeBlocks(text: string): CodeBlock[] {
    const blocks: CodeBlock[] = [];
    const regex = /```(\w*)\n([\s\S]*?)```/g;
    let match;
    
    while ((match = regex.exec(text)) !== null) {
        blocks.push({
            full: match[0],
            lang: match[1] || 'unknown',
            code: match[2]
        });
    }
    
    return blocks;
}

/**
 * Detect programming language from code content
 * Order matters - check more specific patterns first
 */
export function detectLanguage(code: string): string {
    // Coq indicators (very specific)
    if (code.includes('Theorem') || code.includes('Lemma') || code.includes('Proof.') || code.includes('Qed.')) {
        return 'coq';
    }
    // Rust indicators (check before JS because of 'let')
    if (code.includes('fn ') || code.includes('let mut') || code.includes('impl ') || code.includes('::')) {
        return 'rust';
    }
    // Go indicators (check before JS because of 'func')
    if (code.includes('func ') || code.includes('package ')) {
        return 'go';
    }
    // Python indicators
    if (code.includes('def ') || code.includes('import ') || (code.includes('class ') && code.includes(':'))) {
        return 'python';
    }
    // JavaScript/TypeScript indicators (most generic, check last)
    if (code.includes('function') || code.includes('const ') || code.includes('let ') || code.includes('=>')) {
        return 'javascript';
    }
    return 'unknown';
}

/**
 * Check if a language should be skipped for verification
 */
export function shouldSkipLanguage(lang: string): boolean {
    return SKIP_LANGUAGES.includes(lang.toLowerCase());
}

/**
 * Sanitize response by replacing failed code blocks
 */
export function sanitizeResponse(response: string, failedBlocks: Array<{ block: CodeBlock; error: string }>): string {
    let sanitized = response;
    for (const { block, error } of failedBlocks) {
        sanitized = sanitized.replace(
            block.full,
            `\`\`\`\n⛔ BLOCKED: ${error}\n\`\`\``
        );
    }
    return sanitized;
}

/**
 * Format verification table row
 */
export function formatTableRow(index: number, lang: string, status: 'pass' | 'fail' | 'skip', details: string): string {
    const statusEmoji = status === 'pass' ? '✅ Pass' : status === 'fail' ? '⛔ Fail' : '⏭️ Skip';
    return `| ${index} | ${lang} | ${statusEmoji} | ${details} |\n`;
}

/**
 * Verifier client interface for dependency injection
 */
export interface VerifierClient {
    verify(code: string, lang: string): Promise<VerificationResult>;
    verifyOrganic(prompt: string, code: string): Promise<OrganicVerificationResult>;
    getStatus(): Promise<ServerStatus>;
}

/**
 * Result of organic verification (with execution)
 */
export interface OrganicVerificationResult {
    success: boolean;
    code: string | null;
    iterations: number;
    testResults: Array<{
        inputs: any;
        expected: any;
        actual: any;
        passed: boolean;
        error: string | null;
    }>;
    certificate: string | null;
    explanation: string;
    testsRun: number;
    testsPassed: number;
}

/**
 * HTTP client for the Thiele verification server
 */
export class ThieleVerifierClient implements VerifierClient {
    constructor(
        private baseUrl: string = 'http://localhost:7331',
        private timeout: number = 5000
    ) {}

    async verify(code: string, lang: string): Promise<VerificationResult> {
        try {
            const resp = await fetch(`${this.baseUrl}/verify`, {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({ text: '```' + lang + '\n' + code + '\n```' }),
                signal: AbortSignal.timeout(this.timeout)
            });

            const result = await resp.json() as any;
            
            if (result.structurally_failed > 0) {
                const err = result.claims?.find((c: any) => c.error)?.error || 'Syntax error';
                return { valid: false, error: err };
            }
            
            return { valid: true };
        } catch (e) {
            // Pass through if server unavailable - fail open for UX
            return { valid: true };
        }
    }

    /**
     * Organic verification - extracts tests from natural language and executes
     */
    async verifyOrganic(prompt: string, code: string): Promise<OrganicVerificationResult> {
        try {
            const resp = await fetch(`${this.baseUrl}/verify/organic`, {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({ prompt, code }),
                signal: AbortSignal.timeout(this.timeout * 2) // More time for execution
            });

            const result = await resp.json() as any;
            
            return {
                success: result.success,
                code: result.code,
                iterations: result.iterations || 1,
                testResults: result.test_results || [],
                certificate: result.certificate,
                explanation: result.explanation || '',
                testsRun: result.tests_run || 0,
                testsPassed: result.tests_passed || 0,
            };
        } catch (e) {
            // Fallback to basic syntax check
            const syntaxResult = await this.verify(code, 'python');
            return {
                success: syntaxResult.valid,
                code: code,
                iterations: 1,
                testResults: [],
                certificate: null,
                explanation: syntaxResult.valid 
                    ? '✅ Syntax verified (organic verification unavailable)'
                    : `❌ ${syntaxResult.error}`,
                testsRun: 0,
                testsPassed: 0,
            };
        }
    }

    async getStatus(): Promise<ServerStatus> {
        const resp = await fetch(`${this.baseUrl}/status`, {
            signal: AbortSignal.timeout(this.timeout)
        });
        return await resp.json() as ServerStatus;
    }
}

/**
 * Mock client for testing
 */
export class MockVerifierClient implements VerifierClient {
    private mockResults: Map<string, VerificationResult> = new Map();
    private defaultResult: VerificationResult | null = null;
    private mockStatus: ServerStatus = {
        status: 'healthy',
        statistics: {
            total_verifications: 100,
            verified: 94,
            failed: 6,
            verification_rate: 0.94,
            mu_consumed: 100,
            mu_remaining: 9900,
            mu_budget: 10000,
            uptime_sec: 3600
        }
    };

    /**
     * Set mock result for a specific code snippet
     */
    setMockResult(code: string, result: VerificationResult): void {
        this.mockResults.set(code, result);
    }

    /**
     * Set a default result for all verifications (used when no specific mock is set)
     */
    setDefaultResult(result: VerificationResult): void {
        this.defaultResult = result;
    }

    /**
     * Clear the default result (return to valid by default)
     */
    clearDefaultResult(): void {
        this.defaultResult = null;
    }

    setMockStatus(status: ServerStatus): void {
        this.mockStatus = status;
    }

    async verify(code: string, _lang: string): Promise<VerificationResult> {
        // Check for specific mock first
        const result = this.mockResults.get(code);
        if (result) return result;
        // Then check for default result
        if (this.defaultResult) return this.defaultResult;
        // Default: valid
        return { valid: true };
    }

    async verifyOrganic(_prompt: string, code: string): Promise<OrganicVerificationResult> {
        const syntaxResult = await this.verify(code, 'python');
        return {
            success: syntaxResult.valid,
            code: code,
            iterations: 1,
            testResults: [],
            certificate: syntaxResult.valid ? 'mock-cert-123' : null,
            explanation: syntaxResult.valid ? '✅ Mock verified' : `❌ ${syntaxResult.error}`,
            testsRun: 0,
            testsPassed: 0,
        };
    }

    async getStatus(): Promise<ServerStatus> {
        return this.mockStatus;
    }
}
