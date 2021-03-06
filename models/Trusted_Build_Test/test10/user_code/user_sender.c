#include <smaccm_sender.h>
#include <sender.h>
#include <inttypes.h>

void periodic_ping(const int64_t * periodic_100_ms) {

   printf("sender: periodic dispatch received (%" PRI64 ").  Writing to receiver \n", * periodic_100_ms);
   
   uint32_t test_data;
   test_data = *periodic_100_ms / 10;
   
   printf("sender: sending test data: (%d) to receiver \n", test_data);
   
   bool result = ping_Output1(&test_data);
   printf("first attempt at pinging receiver was: %d. \n", result); 

   test_data = 20;
   result = ping_Output1(&test_data);
   printf("second attempt at pinging receiver was: %d. \n", result); 

}
