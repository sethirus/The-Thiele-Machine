const { execSync } = require('child_process');
try {
  const result = execSync(
    'cd /workspaces/The-Thiele-Machine/coq && /usr/bin/coqc -Q . Kernel -Q kami_hw KamiHW -Q ../vendor/kami/Kami Kami ThieleMachineComplete.v 2>&1',
    { timeout: 600000, encoding: 'utf-8', maxBuffer: 50 * 1024 * 1024 }
  );
  console.log("OUTPUT:", result);
} catch(e) {
  console.log("STDOUT:", e.stdout);
  console.log("STDERR:", e.stderr);
  console.log("STATUS:", e.status);
  console.log("ERROR:", e.message);
}
const fs = require('fs');
const voPath = '/workspaces/The-Thiele-Machine/coq/ThieleMachineComplete.vo';
if (fs.existsSync(voPath)) {
  const stat = fs.statSync(voPath);
  console.log("VO FILE: exists, size:", stat.size, "mtime:", stat.mtime);
} else {
  console.log("VO FILE: not found");
}
