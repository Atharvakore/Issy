#include <stdlib.h>
void read_inputs() { /* INSERT HERE */ }
int x;
void main() {
  {
    int prog_counter;
    prog_counter = 0;
    x = 10;
    for(;;)
      {
        if ((prog_counter == 1))
          {
            read_inputs();
            {
            int temp_copy_prog_counter = 1;
            int temp_copy_x = 0;
            prog_counter = temp_copy_prog_counter;
            x = temp_copy_x;
            }
            continue;
          }
        if ((prog_counter == 0))
          {
            for(;;)
              {
                if ((prog_counter == 1))
                  break;
                if (((prog_counter == 0) && (x == 0)))
                  {
                    read_inputs();
                    prog_counter = 1;
                    continue;
                  }
                if ((prog_counter == 0))
                  {
                    {
                      int init_x;
                      for(;;)
                        {
                          if ((prog_counter == 2))
                            prog_counter = 0;
                          if ((prog_counter == 0))
                            init_x = x;
                          if (((prog_counter == 0) && (x == 0)))
                            {
                              prog_counter = 0;
                              break;
                            }
                          if (((prog_counter == 0) && (((1 <= x) && (x < 11)&& (1 <= init_x)&& (0 <= (init_x + (-1 * x)))) || (x == 1))))
                            {
                              read_inputs();
                              {
                              int temp_copy_prog_counter = 2;
                              int temp_copy_x = ((x == 1) ? 0 : (((1 <= x) && (x < 10)&& (2 <= (init_x + (-1 * x)))) ? (-1 * (-1 + (-1 * x))) : (-1 * (1 + (-1 * x)))));
                              prog_counter = temp_copy_prog_counter;
                              x = temp_copy_x;
                              }
                              continue;
                            }
                          abort();
                        }
                    }
                    continue;
                  }
                abort();
              }
            continue;
          }
        if ((prog_counter == 1))
          {
            for(;;)
              {
                if ((prog_counter == 1))
                  break;
                if (((prog_counter == 0) && (x == 0)))
                  {
                    read_inputs();
                    prog_counter = 1;
                    continue;
                  }
                if ((prog_counter == 0))
                  {
                    {
                      int init_x;
                      for(;;)
                        {
                          if ((prog_counter == 2))
                            prog_counter = 0;
                          if ((prog_counter == 0))
                            init_x = x;
                          if (((prog_counter == 0) && (x == 0)))
                            {
                              prog_counter = 0;
                              break;
                            }
                          if (((prog_counter == 0) && (((1 <= x) && (x < 11)&& (1 <= init_x)&& (0 <= (init_x + (-1 * x)))) || (x == 1))))
                            {
                              read_inputs();
                              {
                              int temp_copy_prog_counter = 2;
                              int temp_copy_x = ((x == 1) ? 0 : (((1 <= x) && (x < 10)&& (2 <= (init_x + (-1 * x)))) ? (-1 * (-1 + (-1 * x))) : (-1 * (1 + (-1 * x)))));
                              prog_counter = temp_copy_prog_counter;
                              x = temp_copy_x;
                              }
                              continue;
                            }
                          abort();
                        }
                    }
                    continue;
                  }
                abort();
              }
            continue;
          }
        if (((prog_counter == 0) && (0 <= x)&& (x < 11)))
          {
            read_inputs();
            {
            int temp_copy_prog_counter = (((1 <= x) && (x < 12)) ? 0 : 1);
            int temp_copy_x = ((x < 1) ? x : (((1 <= x) && (x < 10)) ? (-1 * (-1 + (-1 * x))) : (-1 * (1 + (-1 * x)))));
            prog_counter = temp_copy_prog_counter;
            x = temp_copy_x;
            }
            continue;
          }
        if ((prog_counter == 1))
          {
            read_inputs();
            {
            int temp_copy_prog_counter = 1;
            int temp_copy_x = 0;
            prog_counter = temp_copy_prog_counter;
            x = temp_copy_x;
            }
            continue;
          }
        abort();
      }
  }
}
