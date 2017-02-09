#include <math.h>
#include <sha256_main_i.h>
#include <stdint.h> // for uint64_t

uint64_t GetRDTSC() {
  //VS on x64 doesn't support inline assembly
   //__asm {
   //   ; Flush the pipeline
   //   XOR eax, eax
   //   CPUID
   //   ; Get RDTSC counter in edx:eax
   //   RDTSC
   //}
#ifdef _WIN32
  int CPUInfo[4];
  int InfoType = 0;
   __cpuid(CPUInfo, InfoType); // Serialize the pipeline
   return (unsigned __int64)__rdtsc();
#else
  uint64_t rv;
  __asm__ (
    "push    %%ebx;"
    "cpuid;"
    "pop    %%ebx;"
    :::"%eax","%ecx","%edx");
  __asm__ __volatile__ ("rdtsc" : "=A" (rv));
  return (rv);
#endif // _WIN32
}

double getTimeSeconds(uint64_t cycles) {
  // Calibrate frequency
  uint64_t startTime = GetRDTSC();
  Sleep(200);  // Sleep for 200ms
  uint64_t stopTime = GetRDTSC();

  double cpuFreq = (stopTime - startTime) / (200 / 1000.0);

  printf("Measured CPU at %f GHz\n", cpuFreq/pow(10.0, 9));

  return cycles / cpuFreq;
}


void speed_test(int num_trials, int buffer_size) {
  uint32_t digest[8];

  uint8_t* buffer = malloc(sizeof(uint8_t)*buffer_size);

  uint64_t total_cycles = 0;

  for (int trial = 0; trial < num_trials; trial++) {
    uint64_t start = GetRDTSC();
    sha256_main_i_SHA256_Complete(buffer, 0, buffer_size, digest);
    uint64_t end = GetRDTSC();
    total_cycles += end - start;
  }

  double seconds = getTimeSeconds(total_cycles) / (float)num_trials;
  double micro_seconds = seconds * pow(10.0,6);
  printf("Computing SHA on a %d byte buffer took %0.2f cycles ~= %0.2f microseconds\n",
         buffer_size, total_cycles / (float) num_trials, micro_seconds);
  double blocks = 1.0 / seconds;
  printf("That's %0.1f blocks per second\n", blocks);
  printf("That's %0.1f kbytes per second\n", blocks * buffer_size / 1000.0); }

void demo()
{
  uint8_t bytes[3];
  bytes[0] = 'a';
  bytes[1] = 'b';
  bytes[2] = 'c';

  uint32_t digest[8];


sha256_main_i_SHA256_Complete(bytes, 0, 3, digest);

  for (int i = 0; i < 8; i++) {
    printf("%x", digest[i]);
    //printf("%x ", digest[i]);
  }
  printf("\n");
}

void main()
{
  demo();
  //speed_test(100000, 8192);
  //speed_test(10000, 10*1024);
}

