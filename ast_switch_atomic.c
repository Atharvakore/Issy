#include <stdio.h>
#include <stdlib.h>

// Stub for the 'Read' operations in the AST
void read() {
    // Implementation depends on target environment
}

int main() {
    // Declarations
    int __tmp_init_x;
    int __tmp_init_x__lift_1;
    int __tmp_prog_counter;
    int __tmp_x;
    int prog_counter;
    int init_x;
    int init_x__lift_1;
    int x; 

    // Initial Assignments
    prog_counter = 0;
    x = 10;

    // Infinite Loop -> Switch
    while (1) {
        switch (prog_counter) {
            case 0:
                __tmp_init_x = init_x;
                __tmp_init_x__lift_1 = init_x__lift_1;
                __tmp_prog_counter = prog_counter;
                __tmp_x = x;

                while (1) {
                    switch (prog_counter) {
                        case 0:
                            __tmp_init_x = init_x;
                            __tmp_init_x__lift_1 = init_x__lift_1;
                            __tmp_prog_counter = prog_counter;
                            __tmp_x = x;

                            if (x == 0) {
                                read();
                                __tmp_prog_counter = 1;
                                init_x = __tmp_init_x;
                                init_x__lift_1 = __tmp_init_x__lift_1;
                                prog_counter = __tmp_prog_counter;
                                x = __tmp_x;
                                continue;
                            }

                            while (1) {
                                switch (prog_counter) {
                                    case 0:
                                        __tmp_init_x = init_x;
                                        __tmp_init_x__lift_1 = init_x__lift_1;
                                        __tmp_prog_counter = prog_counter;
                                        __tmp_x = x;
                                        __tmp_init_x = x;

                                        if (x == 0) {
                                            __tmp_prog_counter = 0;
                                            init_x = __tmp_init_x;
                                            init_x__lift_1 = __tmp_init_x__lift_1;
                                            prog_counter = __tmp_prog_counter;
                                            x = __tmp_x;
                                            break;
                                        }

                                        if (((((1 <= x) && (x < 11)) && (1 <= init_x)) && (0 <= (init_x + (-1 * x)))) || (x == 1)) {
                                            read();
                                            __tmp_prog_counter = 2;
                                            
                                            if (x == 1) {
                                                __tmp_x = 0;
                                            }
                                            
                                            if (!(x == 1)) {
                                                if ((1 <= x) && ((x < 10) && (2 <= (init_x + (-1 * x))))) {
                                                    __tmp_x = x + 1;
                                                }
                                                if (!((1 <= x) && ((x < 10) && (2 <= (init_x + (-1 * x)))))) {
                                                    __tmp_x = -1 + x;
                                                }
                                            }
                                        }
                                        
                                        init_x = __tmp_init_x;
                                        init_x__lift_1 = __tmp_init_x__lift_1;
                                        prog_counter = __tmp_prog_counter;
                                        x = __tmp_x;
                                        continue;

                                    case 2:
                                        __tmp_init_x = init_x;
                                        __tmp_init_x__lift_1 = init_x__lift_1;
                                        __tmp_prog_counter = prog_counter;
                                        __tmp_x = x;
                                        __tmp_prog_counter = 0;
                                        init_x = __tmp_init_x;
                                        init_x__lift_1 = __tmp_init_x__lift_1;
                                        prog_counter = __tmp_prog_counter;
                                        x = __tmp_x;
                                        continue;

                                    default:
                                        abort();
                                }
                            }

                            init_x = __tmp_init_x;
                            init_x__lift_1 = __tmp_init_x__lift_1;
                            prog_counter = __tmp_prog_counter;
                            x = __tmp_x;
                            continue;

                        case 1:
                            __tmp_init_x = init_x;
                            __tmp_init_x__lift_1 = init_x__lift_1;
                            __tmp_prog_counter = prog_counter;
                            __tmp_x = x;
                            init_x = __tmp_init_x;
                            init_x__lift_1 = __tmp_init_x__lift_1;
                            prog_counter = __tmp_prog_counter;
                            x = __tmp_x;
                            break;

                        default:
                            abort();
                    }
                }

                init_x = __tmp_init_x;
                init_x__lift_1 = __tmp_init_x__lift_1;
                prog_counter = __tmp_prog_counter;
                x = __tmp_x;
                continue;

            case 1:
                __tmp_init_x = init_x;
                __tmp_init_x__lift_1 = init_x__lift_1;
                __tmp_prog_counter = prog_counter;
                __tmp_x = x;
                read();
                __tmp_prog_counter = 1;
                __tmp_x = 0;
                init_x = __tmp_init_x;
                init_x__lift_1 = __tmp_init_x__lift_1;
                prog_counter = __tmp_prog_counter;
                x = __tmp_x;
                continue;

            default:
                abort();
        }
    }

    return 0;
}