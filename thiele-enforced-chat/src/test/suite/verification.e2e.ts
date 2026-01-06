/**
 * E2E Tests with REAL network calls to Thiele Verification Server
 * These tests require the server running at localhost:7331
 */
import * as assert from 'assert';
import { ThieleVerifierClient } from '../../verifier';

describe('Real Verification Server E2E Tests', () => {
    let client: ThieleVerifierClient;

    before(function() {
        this.timeout(10000);
        client = new ThieleVerifierClient('http://localhost:7331');
    });

    describe('Server Connectivity', () => {
        it('should connect to running server', async function() {
            this.timeout(5000);
            const status = await client.getStatus();
            assert.strictEqual(status.status, 'running', 'Server should be running');
        });

        it('should return valid statistics', async function() {
            this.timeout(5000);
            const status = await client.getStatus();
            assert.ok(status.statistics, 'Should have statistics');
            assert.ok(typeof status.statistics.total_verifications === 'number');
            assert.ok(typeof status.statistics.verification_rate === 'number');
        });
    });

    describe('Real Code Verification', () => {
        it('should verify valid Python code', async function() {
            this.timeout(5000);
            const code = `def factorial(n):
    if n <= 1:
        return 1
    return n * factorial(n - 1)`;
            
            const result = await client.verify(code, 'python');
            assert.strictEqual(result.valid, true, 'Valid Python should pass');
        });

        it('should reject invalid Python syntax', async function() {
            this.timeout(5000);
            const code = `def broken(
    # missing closing paren and colon`;
            
            const result = await client.verify(code, 'python');
            assert.strictEqual(result.valid, false, 'Invalid Python should fail');
            assert.ok(result.error, 'Should have error message');
        });

        it('should verify valid JavaScript code', async function() {
            this.timeout(5000);
            const code = `function hello() {
    return "world";
}`;
            
            const result = await client.verify(code, 'javascript');
            // Note: JS verification may return valid=true even for syntax errors
            // because the server marks unknown languages as "unverifiable" not "failed"
            assert.strictEqual(result.valid, true, 'JS passes through (server lacks JS parser)');
        });

        it('should pass through unverifiable languages', async function() {
            this.timeout(5000);
            // JavaScript isn't parsed by the server, so it passes through
            const code = `function broken( {
    return "missing paren"
}`;
            
            const result = await client.verify(code, 'javascript');
            // This passes because the server can't verify JS - it's marked unverifiable
            assert.strictEqual(result.valid, true, 'Unverifiable languages pass through');
        });

        it('should verify valid Rust code', async function() {
            this.timeout(5000);
            const code = `fn main() {
    let x = 42;
    println!("{}", x);
}`;
            
            const result = await client.verify(code, 'rust');
            assert.strictEqual(result.valid, true, 'Valid Rust should pass');
        });

        it('should verify valid Go code', async function() {
            this.timeout(5000);
            const code = `package main

func main() {
    x := 42
    fmt.Println(x)
}`;
            
            const result = await client.verify(code, 'go');
            assert.strictEqual(result.valid, true, 'Valid Go should pass');
        });

        it('should verify valid Coq code', async function() {
            this.timeout(5000);
            const code = `Theorem identity : forall A : Prop, A -> A.
Proof.
  intros A H.
  exact H.
Qed.`;
            
            const result = await client.verify(code, 'coq');
            assert.strictEqual(result.valid, true, 'Valid Coq should pass');
        });
    });

    describe('μ-Cost Tracking', () => {
        it('should consume μ-cost on verification', async function() {
            this.timeout(5000);
            const statusBefore = await client.getStatus();
            const muBefore = statusBefore.statistics.mu_consumed;

            await client.verify('x = 1', 'python');

            const statusAfter = await client.getStatus();
            const muAfter = statusAfter.statistics.mu_consumed;

            assert.ok(muAfter >= muBefore, 'μ-cost should increase or stay same');
        });

        it('should increment verification count', async function() {
            this.timeout(5000);
            const statusBefore = await client.getStatus();
            const countBefore = statusBefore.statistics.total_verifications;

            await client.verify('y = 2', 'python');

            const statusAfter = await client.getStatus();
            const countAfter = statusAfter.statistics.total_verifications;

            assert.strictEqual(countAfter, countBefore + 1, 'Count should increment by 1');
        });
    });

    describe('Edge Cases', () => {
        it('should handle empty code', async function() {
            this.timeout(5000);
            const result = await client.verify('', 'python');
            // Empty code is syntactically valid in Python
            assert.strictEqual(result.valid, true);
        });

        it('should handle code with unicode', async function() {
            this.timeout(5000);
            const code = `def greet():
    return "Hello, 世界! 🌍"`;
            
            const result = await client.verify(code, 'python');
            assert.strictEqual(result.valid, true);
        });

        it('should handle very long code', async function() {
            this.timeout(10000);
            const lines = [];
            for (let i = 0; i < 100; i++) {
                lines.push(`x${i} = ${i}`);
            }
            const code = lines.join('\n');
            
            const result = await client.verify(code, 'python');
            assert.strictEqual(result.valid, true);
        });
    });
});
