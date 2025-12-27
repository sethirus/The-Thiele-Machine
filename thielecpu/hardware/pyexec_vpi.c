// VPI module implementing $pyexec for Icarus builds without $system.
//
// Registers a custom system task:
//   $pyexec(code_addr, result);
//
// It executes the repo's Python bridge in single-shot mode and returns the
// integer result (rc / digest) through the output argument.
//
// The repo root is read from the simulator argv via +REPO_ROOT=<path>.

#include <vpi_user.h>

#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

static int find_repo_root(char *out, size_t out_sz) {
    s_vpi_vlog_info info;
    if (!vpi_get_vlog_info(&info)) {
        return 0;
    }

    const char *prefix = "+REPO_ROOT=";
    size_t prefix_len = strlen(prefix);

    for (int i = 0; i < info.argc; i++) {
        const char *arg = info.argv[i];
        if (!arg) {
            continue;
        }
        if (strncmp(arg, prefix, prefix_len) == 0) {
            const char *val = arg + prefix_len;
            if (!val || !*val) {
                continue;
            }
            snprintf(out, out_sz, "%s", val);
            return 1;
        }
    }

    return 0;
}

static int run_bridge_single_shot(uint32_t code_addr, const char *repo_root, uint32_t *out_u32) {
    // Run: python3 <repo_root>/thielecpu/hardware/pyexec_bridge.py --repo-root <repo_root>
    //      --code-addr 0x.... --print-result
    // Capture stdout and parse a single integer.

    char script_path[4096];
    int nsp = snprintf(
        script_path,
        sizeof(script_path),
        "%s/thielecpu/hardware/pyexec_bridge.py",
        repo_root
    );
    if (nsp < 0 || (size_t)nsp >= sizeof(script_path)) {
        return 0;
    }

    char code_buf[32];
    snprintf(code_buf, sizeof(code_buf), "0x%08x", (unsigned)code_addr);

    const char *argv_exec[] = {
        "python3",
        script_path,
        "--repo-root",
        repo_root,
        "--code-addr",
        code_buf,
        "--print-result",
        NULL,
    };

    int pipefd[2];
    if (pipe(pipefd) != 0) {
        return 0;
    }

    pid_t pid = fork();
    if (pid < 0) {
        close(pipefd[0]);
        close(pipefd[1]);
        return 0;
    }

    if (pid == 0) {
        // Child
        (void)dup2(pipefd[1], STDOUT_FILENO);
        (void)dup2(pipefd[1], STDERR_FILENO); // keep logs available if parsing fails
        close(pipefd[0]);
        close(pipefd[1]);
        execvp(argv_exec[0], (char *const *)argv_exec);
        _exit(127);
    }

    // Parent
    close(pipefd[1]);

    char buf[512];
    ssize_t nread = read(pipefd[0], buf, sizeof(buf) - 1);
    close(pipefd[0]);

    int status = 0;
    (void)waitpid(pid, &status, 0);

    if (nread <= 0) {
        return 0;
    }

    buf[nread] = '\0';

    // Parse first integer in output.
    char *endp = NULL;
    errno = 0;
    long long val = strtoll(buf, &endp, 0);
    if (errno != 0 || endp == buf) {
        return 0;
    }

    *out_u32 = (uint32_t)val;
    return 1;
}

static PLI_INT32 pyexec_calltf(PLI_BYTE8 *user_data) {
    (void)user_data;

    vpiHandle systf = vpi_handle(vpiSysTfCall, NULL);
    vpiHandle args_iter = vpi_iterate(vpiArgument, systf);
    if (!args_iter) {
        vpi_printf("[VPI] $pyexec: missing args\n");
        return 0;
    }

    vpiHandle h_code = vpi_scan(args_iter);
    vpiHandle h_out = vpi_scan(args_iter);
    if (!h_code || !h_out) {
        vpi_printf("[VPI] $pyexec: expected (code_addr, out)\n");
        return 0;
    }

    s_vpi_value v_code;
    v_code.format = vpiIntVal;
    vpi_get_value(h_code, &v_code);
    uint32_t code_addr = (uint32_t)v_code.value.integer;

    char repo_root[4096];
    if (!find_repo_root(repo_root, sizeof(repo_root))) {
        vpi_printf("[VPI] $pyexec: missing +REPO_ROOT=<path> plusarg\n");
        // Write a recognizable failure code.
        s_vpi_value v_out;
        v_out.format = vpiIntVal;
        v_out.value.integer = (int32_t)0xFFFFFFFD;
        vpi_put_value(h_out, &v_out, NULL, vpiNoDelay);
        return 0;
    }

    uint32_t out_u32 = 0;
    if (!run_bridge_single_shot(code_addr, repo_root, &out_u32)) {
        vpi_printf("[VPI] $pyexec: bridge failed for code_addr=0x%08x\n", (unsigned)code_addr);
        out_u32 = 0xFFFFFFFC;
    }

    s_vpi_value v_out;
    v_out.format = vpiIntVal;
    v_out.value.integer = (int32_t)out_u32;
    vpi_put_value(h_out, &v_out, NULL, vpiNoDelay);

    return 0;
}

static PLI_INT32 pyexec_compiletf(PLI_BYTE8 *user_data) {
    (void)user_data;
    return 0;
}

void pyexec_register(void) {
    s_vpi_systf_data tf;
    memset(&tf, 0, sizeof(tf));

    tf.type = vpiSysTask;
    tf.tfname = "$pyexec";
    tf.calltf = pyexec_calltf;
    tf.compiletf = pyexec_compiletf;
    tf.sizetf = 0;
    tf.user_data = 0;

    vpi_register_systf(&tf);
}

void (*vlog_startup_routines[])(void) = {
    pyexec_register,
    0,
};
