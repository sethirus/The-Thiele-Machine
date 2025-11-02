/* toycc.c - Minimal C Compiler for Trusting Trust Demo
 *
 * This is a toy compiler that demonstrates the Ken Thompson 
 * "Reflections on Trusting Trust" attack. It compiles a minimal 
 * subset of C to demonstrate that two different compilers can
 * produce byte-identical output when no backdoor is present.
 *
 * Supports: basic arithmetic, variables, if/while, print
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#define MAX_CODE 4096
#define MAX_VARS 26  /* a-z */

typedef struct {
    char *input;
    int pos;
    int vars[MAX_VARS];
    char code[MAX_CODE];
    int code_pos;
} Compiler;

void error(const char *msg) {
    fprintf(stderr, "Error: %s\n", msg);
    exit(1);
}

void skip_whitespace(Compiler *c) {
    while (c->input[c->pos] && isspace(c->input[c->pos])) {
        c->pos++;
    }
}

int parse_number(Compiler *c) {
    skip_whitespace(c);
    if (!isdigit(c->input[c->pos])) {
        error("Expected number");
    }
    int val = 0;
    while (isdigit(c->input[c->pos])) {
        val = val * 10 + (c->input[c->pos] - '0');
        c->pos++;
    }
    return val;
}

char parse_var(Compiler *c) {
    skip_whitespace(c);
    if (!islower(c->input[c->pos])) {
        error("Expected variable (a-z)");
    }
    return c->input[c->pos++];
}

void emit(Compiler *c, const char *fmt, ...) {
    va_list args;
    va_start(args, fmt);
    c->code_pos += vsnprintf(c->code + c->code_pos, 
                             MAX_CODE - c->code_pos, fmt, args);
    va_end(args);
}

void parse_statement(Compiler *c);

int parse_expr(Compiler *c) {
    skip_whitespace(c);
    
    int val;
    if (isdigit(c->input[c->pos])) {
        val = parse_number(c);
    } else if (islower(c->input[c->pos])) {
        char var = parse_var(c);
        val = c->vars[var - 'a'];
    } else {
        error("Expected expression");
    }
    
    skip_whitespace(c);
    while (c->input[c->pos] == '+' || c->input[c->pos] == '-' ||
           c->input[c->pos] == '*' || c->input[c->pos] == '/') {
        char op = c->input[c->pos++];
        int right = parse_expr(c);
        
        switch (op) {
            case '+': val += right; break;
            case '-': val -= right; break;
            case '*': val *= right; break;
            case '/': 
                if (right == 0) error("Division by zero");
                val /= right;
                break;
        }
    }
    
    return val;
}

void parse_assignment(Compiler *c) {
    char var = parse_var(c);
    skip_whitespace(c);
    
    if (c->input[c->pos] != '=') {
        error("Expected '='");
    }
    c->pos++;
    
    int val = parse_expr(c);
    c->vars[var - 'a'] = val;
    
    emit(c, "    %c = %d;\n", var, val);
    
    skip_whitespace(c);
    if (c->input[c->pos] == ';') {
        c->pos++;
    }
}

void parse_print(Compiler *c) {
    /* Skip 'print' keyword */
    c->pos += 5;
    skip_whitespace(c);
    
    if (c->input[c->pos] != '(') {
        error("Expected '(' after print");
    }
    c->pos++;
    
    char var = parse_var(c);
    
    skip_whitespace(c);
    if (c->input[c->pos] != ')') {
        error("Expected ')'");
    }
    c->pos++;
    
    emit(c, "    printf(\"%%d\\n\", %c);\n", var);
    
    skip_whitespace(c);
    if (c->input[c->pos] == ';') {
        c->pos++;
    }
}

void parse_block(Compiler *c) {
    skip_whitespace(c);
    if (c->input[c->pos] != '{') {
        error("Expected '{'");
    }
    c->pos++;
    
    emit(c, "{\n");
    
    while (1) {
        skip_whitespace(c);
        if (c->input[c->pos] == '}') {
            c->pos++;
            break;
        }
        parse_statement(c);
    }
    
    emit(c, "}\n");
}

void parse_statement(Compiler *c) {
    skip_whitespace(c);
    
    if (strncmp(c->input + c->pos, "print", 5) == 0) {
        parse_print(c);
    } else if (strncmp(c->input + c->pos, "if", 2) == 0) {
        c->pos += 2;
        emit(c, "    if ");
        parse_block(c);
    } else if (strncmp(c->input + c->pos, "while", 5) == 0) {
        c->pos += 5;
        emit(c, "    while ");
        parse_block(c);
    } else if (islower(c->input[c->pos])) {
        parse_assignment(c);
    }
}

void compile(const char *input, char *output) {
    Compiler c = {0};
    c.input = (char *)input;
    
    /* Emit header */
    emit(&c, "#include <stdio.h>\nint main() {\n");
    emit(&c, "    int a=0,b=0,c=0,d=0,e=0,f=0,g=0,h=0,i=0,j=0,k=0,l=0,m=0;\n");
    emit(&c, "    int n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0;\n");
    
    /* Parse statements */
    while (c.input[c.pos]) {
        parse_statement(&c);
    }
    
    /* Emit footer */
    emit(&c, "    return 0;\n}\n");
    
    strcpy(output, c.code);
}

int main(int argc, char **argv) {
    if (argc != 3) {
        fprintf(stderr, "Usage: %s <input.c> <output.c>\n", argv[0]);
        return 1;
    }
    
    FILE *in = fopen(argv[1], "r");
    if (!in) {
        perror("Failed to open input");
        return 1;
    }
    
    char input[MAX_CODE];
    size_t len = fread(input, 1, MAX_CODE - 1, in);
    input[len] = '\0';
    fclose(in);
    
    char output[MAX_CODE];
    compile(input, output);
    
    FILE *out = fopen(argv[2], "w");
    if (!out) {
        perror("Failed to open output");
        return 1;
    }
    
    fprintf(out, "%s", output);
    fclose(out);
    
    printf("Compiled %s -> %s\n", argv[1], argv[2]);
    return 0;
}
