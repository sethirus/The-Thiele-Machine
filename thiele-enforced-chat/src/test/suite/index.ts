/**
 * E2E Test Suite Index
 * Loads and runs all E2E tests in the VS Code Extension Host
 */
import * as path from 'path';
import Mocha from 'mocha';
import { glob } from 'glob';

export async function run(): Promise<void> {
    // Create the mocha test
    const mocha = new Mocha({
        ui: 'bdd',
        color: true,
        timeout: 60000 // 60 second timeout for E2E tests
    });

    const testsRoot = path.resolve(__dirname, '.');

    // Find all test files
    const files = await glob('**/**.e2e.js', { cwd: testsRoot });
    
    // Add files to the test suite
    files.forEach(f => mocha.addFile(path.resolve(testsRoot, f)));

    return new Promise<void>((resolve, reject) => {
        try {
            // Run the mocha test
            mocha.run(failures => {
                if (failures > 0) {
                    reject(new Error(`${failures} tests failed.`));
                } else {
                    resolve();
                }
            });
        } catch (err) {
            console.error(err);
            reject(err);
        }
    });
}
