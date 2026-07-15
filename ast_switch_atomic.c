#include <stdio.h>
#include <stdlib.h>

// Mock read function to handle the "Read" tag in the AST
void read_input(void) {
    // Implement read logic or user input here if needed
}

int main(void) {
    // Declarations
    int __tmp_init_x;
    int __tmp_init_x__lift_1;
    int __tmp_prog_counter;
    int __tmp_x;
    int prog_counter;
    int init_x;
    int init_x__lift_1;
    int x; // Declared to handle assignments to 'x'

    // Initializations
    prog_counter = 0;
    x = 10;

    // Outer Infinite Loop
    while (1) {
        switch (prog_counter) {
            case 0: {
                __tmp_init_x = init_x;
                __tmp_init_x__lift_1 = init_x__lift_1;
                __tmp_prog_counter = prog_counter;
                __tmp_x = x;

                // Inner Infinite Loop 1
                while (1) {
                    switch (prog_counter) {
                        case 0: {
                            __tmp_init_x = init_x;
                            __tmp_init_x__lift_1 = init_x__lift_1;
                            __tmp_prog_counter = prog_counter;
                            __tmp_x = x;

                            if (x == 0) {
                                read_input();
                                __tmp_prog_counter = 1;
                                init_x = __tmp_init_x;
                                init_x__lift_1 = __tmp_init_x__lift_1;
                                prog_counter = __tmp_prog_counter;
                                x = __tmp_x;
                                continue;
                            }

                            // Inner-Inner Infinite Loop
                            while (1) {
                                switch (prog_counter) {
                                    case 0: {
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
                                            break; // Breaks out of Inner-Inner Loop
                                        }

                                        // Nested logic conditions decoded from Func tags
                                        if ((((1 <= x) && (x < 11)) && (1 <= init_x) && (0 <= (init_x + (-1 * x)))) || (x == 1)) {
                                            read_input();
                                            __tmp_prog_counter = 2;

                                            if (x == 1) {
                                                __tmp_x = 0;
                                            }

                                            if (!(x == 1)) {
                                                if ((1 <= x) && (x < 10) && (2 <= (init_x + (-1 * x)))) {
                                                    __tmp_x = x + 1;
                                                }
                                                if (!((1 <= x) && (x < 10) && (2 <= (init_x + (-1 * x))))) {
                                                    __tmp_x = -1 + x;
                                                }
                                            }

                                            init_x = __tmp_init_x;
                                            init_x__lift_1 = __tmp_init_x__lift_1;
                                            prog_counter = __tmp_prog_counter;
                                            x = __tmp_x;
                                            continue;
                                        }

                                        init_x = __tmp_init_x;
                                        init_x__lift_1 = __tmp_init_x__lift_1;
                                        prog_counter = __tmp_prog_counter;
                                        x = __tmp_x;
                                        continue;
                                    }
                                    case 2: {
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
                                    }
                                    default: {
                                        abort();
                                    }
                                }
                            } // End Inner-Inner Loop

                            init_x = __tmp_init_x;
                            init_x__lift_1 = __tmp_init_x__lift_1;
                            prog_counter = __tmp_prog_counter;
                            x = __tmp_x;
                            continue;
                        }
                        case 1: {
                            __tmp_init_x = init_x;
                            __tmp_init_x__lift_1 = init_x__lift_1;
                            __tmp_prog_counter = prog_counter;
                            __tmp_x = x;

                            init_x = __tmp_init_x;
                            init_x__lift_1 = __tmp_init_x__lift_1;
                            prog_counter = __tmp_prog_counter;
                            x = __tmp_x;
                            break; // Breaks out of Inner Loop 1
                        }
                        default: {
                            abort();
                        }
                    }
                } // End Inner Loop 1

                init_x = __tmp_init_x;
                init_x__lift_1 = __tmp_init_x__lift_1;
                prog_counter = __tmp_prog_counter;
                x = __tmp_x;
                continue;
            }
            case 1: {
                __tmp_init_x = init_x;
                __tmp_init_x__lift_1 = init_x__lift_1;
                __tmp_prog_counter = prog_counter;
                __tmp_x = x;

                read_input();
                __tmp_prog_counter = 1;
                __tmp_x = 0;

                init_x = __tmp_init_x;
                init_x__lift_1 = __tmp_init_x__lift_1;
                prog_counter = __tmp_prog_counter;
                x = __tmp_x;
                continue;
            }
            default: {
                abort();
            }
        }
    }

    return 0;
}