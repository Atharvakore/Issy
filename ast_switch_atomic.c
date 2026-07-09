#include <stdio.h>
#include <stdlib.h>

static void READ(void) {
    int ignored;
    (void)scanf("%d", &ignored);
}

int main(void) {
    int __tmp_init_x = 0;
    int __tmp_prog_counter = 0;
    int __tmp_x = 0;
    int init_x = 0;
    int prog_counter = 0;
    int x = 0;
    
    prog_counter = 0;
    x = 10;
    while (1) {
        switch (prog_counter) {
            case 0: {
                __tmp_init_x = init_x;
                __tmp_prog_counter = prog_counter;
                __tmp_x = x;
                while (1) {
                    switch (prog_counter) {
                        case 0: {
                            __tmp_init_x = init_x;
                            __tmp_prog_counter = prog_counter;
                            __tmp_x = x;
                            if (x == 0) {
                                READ();
                                __tmp_prog_counter = 1;
                                init_x = __tmp_init_x;
                                prog_counter = __tmp_prog_counter;
                                x = __tmp_x;
                                continue;
                            }
                            while (1) {
                                switch (prog_counter) {
                                    case 0: {
                                        __tmp_init_x = init_x;
                                        __tmp_prog_counter = prog_counter;
                                        __tmp_x = x;
                                        __tmp_init_x = x;
                                        if (x == 0) {
                                            __tmp_prog_counter = 0;
                                            init_x = __tmp_init_x;
                                            prog_counter = __tmp_prog_counter;
                                            x = __tmp_x;
                                            goto after_loop_3;
                                        }
                                        if (((1 <= x) && ((x < 11) && ((1 <= init_x) && (0 <= (init_x + (-1 * x)))))) || (x == 1)) {
                                            READ();
                                            __tmp_prog_counter = 2;
                                            if (x == 1) {
                                                __tmp_x = 0;
                                            }
                                            if (!(x == 1)) {
                                                if ((1 <= x) && ((x < 10) && (2 <= (init_x + (-1 * x))))) {
                                                    __tmp_x = (x + 1);
                                                }
                                                if (!((1 <= x) && ((x < 10) && (2 <= (init_x + (-1 * x)))))) {
                                                    __tmp_x = (-1 + x);
                                                }
                                            }
                                            init_x = __tmp_init_x;
                                            prog_counter = __tmp_prog_counter;
                                            x = __tmp_x;
                                            continue;
                                        }
                                        init_x = __tmp_init_x;
                                        prog_counter = __tmp_prog_counter;
                                        x = __tmp_x;
                                        continue;
                                        break;
                                    }
                                    case 2: {
                                        __tmp_init_x = init_x;
                                        __tmp_prog_counter = prog_counter;
                                        __tmp_x = x;
                                        __tmp_prog_counter = 0;
                                        init_x = __tmp_init_x;
                                        prog_counter = __tmp_prog_counter;
                                        x = __tmp_x;
                                        continue;
                                        break;
                                    }
                                    default: {
                                        abort();
                                        break;
                                    }
                                }
                            }
                            after_loop_3: ;
                            init_x = __tmp_init_x;
                            prog_counter = __tmp_prog_counter;
                            x = __tmp_x;
                            continue;
                            break;
                        }
                        case 1: {
                            __tmp_init_x = init_x;
                            __tmp_prog_counter = prog_counter;
                            __tmp_x = x;
                            init_x = __tmp_init_x;
                            prog_counter = __tmp_prog_counter;
                            x = __tmp_x;
                            goto after_loop_2;
                            break;
                        }
                        default: {
                            abort();
                            break;
                        }
                    }
                }
                after_loop_2: ;
                init_x = __tmp_init_x;
                prog_counter = __tmp_prog_counter;
                x = __tmp_x;
                continue;
                break;
            }
            case 1: {
                __tmp_init_x = init_x;
                __tmp_prog_counter = prog_counter;
                __tmp_x = x;
                READ();
                __tmp_prog_counter = 1;
                __tmp_x = 0;
                init_x = __tmp_init_x;
                prog_counter = __tmp_prog_counter;
                x = __tmp_x;
                continue;
                break;
            }
            default: {
                abort();
                break;
            }
        }
    }
    after_loop_1: ;
    
    return 0;
}
