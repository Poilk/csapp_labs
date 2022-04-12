#include "cachelab.h"
#include <stdio.h>
#include <getopt.h>
#include <stdlib.h>
#include <memory.h>
#include <limits.h>

#define MAX_CMD_BUFFER_LEN 128
#define MAX_INSTRUCTION_LEN 10
#define MAX_SE 8
#define ADDRESS_SIZE 64
#define MAX_BAV_PER_INS 5

struct CacheLine {
  int modified;
  int t;
  int valid;
  int last_visited_clock;
};

struct CacheInfo {
  int s;
  int E;
  int b;
};

struct AddressInfo {
  unsigned long CT;
  unsigned long CI;
  unsigned long CO;
};

enum CacheBehavior {
  CACHE_BEHAVIOR_UNKNOWN = 0,
  CACHE_BEHAVIOR_HIT = 1,
  CACHE_BEHAVIOR_MISS = 2,
  CACHE_BEHAVIOR_EVICTION = 3,
  CACHE_BEHAVIOR_MAX = 4
};

char *behavior_str[] = {"unknown", "hit", "miss", "eviction"};

struct CacheLine cache[MAX_SE][MAX_SE];
int sys_clock;

int findHitLine(struct CacheInfo cache_info, struct AddressInfo address_info) {
  int find_idx = -1;
  for (int i = 0; i < cache_info.E; i++) {
    struct CacheLine *cur_line_ptr = &cache[address_info.CI][i];
    if (cur_line_ptr->valid && cur_line_ptr->t == address_info.CT) {
      find_idx = i;
      break;
    }
  }
  return find_idx;
}

int findLoadLine(struct CacheInfo cache_info, struct AddressInfo address_info) {
  int find_unused_idx = -1;
  int find_LRU_idx = -1;
  int LRU_clock = INT_MAX;
  for (int i = 0; i < cache_info.E; i++) {
    struct CacheLine *cur_line_ptr = &cache[address_info.CI][i];
    if (!cur_line_ptr->valid) {
      find_unused_idx = i;
      break;
    } else {
      if (cur_line_ptr->last_visited_clock < LRU_clock) {
        LRU_clock = cur_line_ptr->last_visited_clock;
        find_LRU_idx = i;
      }
    }
  }
  return find_unused_idx == -1 ? find_LRU_idx : find_unused_idx;
}

int processInstructor(struct CacheInfo cache_info, struct AddressInfo address_info, char instruction, int behaviors[]) {
  int behavior_cnt = 0;
  if (instruction == 'L' || instruction == 'S') {
    int hit_idx = findHitLine(cache_info, address_info);
    if (hit_idx == -1) {
      int load_idx = findLoadLine(cache_info, address_info);
      struct CacheLine *cur_line_ptr = &cache[address_info.CI][load_idx];
      struct CacheLine load_line = {0, address_info.CT, 1, sys_clock};
      behaviors[behavior_cnt++] = CACHE_BEHAVIOR_MISS;
      if (cur_line_ptr->valid) {
        behaviors[behavior_cnt++] = CACHE_BEHAVIOR_EVICTION;
      }
      *cur_line_ptr = load_line;
    } else {
      struct CacheLine *cur_line_ptr = &cache[address_info.CI][hit_idx];
      cur_line_ptr->last_visited_clock = sys_clock;
      behaviors[behavior_cnt++] = CACHE_BEHAVIOR_HIT;
    }
  } else if (instruction == 'M') {
    int tmp_behaviors[MAX_BAV_PER_INS];
    int tmp_behavior_cnt = processInstructor(cache_info, address_info, 'S', tmp_behaviors);
    for (int i = 0; i < tmp_behavior_cnt; i++) {
      behaviors[behavior_cnt++] = tmp_behaviors[i];
    }
    tmp_behavior_cnt = processInstructor(cache_info, address_info, 'L', tmp_behaviors);
    for (int i = 0; i < tmp_behavior_cnt; i++) {
      behaviors[behavior_cnt++] = tmp_behaviors[i];
    }
  }
  return behavior_cnt;
}

void solove(struct CacheInfo cache_info, char *trace_file, int verbose_mode) {
  memset(cache, 0, sizeof(cache));
  sys_clock = 0;
  FILE *fp = fopen(trace_file, "r");
  char cmd_buffer[MAX_CMD_BUFFER_LEN];
  int behavior_result_cnt[CACHE_BEHAVIOR_MAX + 1] = {0};
  while (fgets(cmd_buffer, MAX_CMD_BUFFER_LEN, fp) != NULL) {
    sys_clock += 1;
    if (cmd_buffer[0] == 'I') {
      continue;
    }
    char instruction_str[MAX_INSTRUCTION_LEN];
    unsigned long address;
    sscanf(cmd_buffer, "%s %lx", instruction_str, &address);
    struct AddressInfo address_info;
    address_info.CT = address >> (cache_info.s + cache_info.b);
    address_info.CI = (address << (ADDRESS_SIZE - cache_info.s - cache_info.b)) >> (ADDRESS_SIZE - cache_info.s);
    address_info.CO = (address << (ADDRESS_SIZE - cache_info.b)) >> (ADDRESS_SIZE - cache_info.b);

    int behaviors[MAX_BAV_PER_INS];
    int behaviors_cnt = processInstructor(cache_info, address_info, instruction_str[0], behaviors);

    if (verbose_mode) {
      printf("%s, %lx, CT %lx, CI %lx, CO %lx ",
             instruction_str,
             address,
             address_info.CT,
             address_info.CI,
             address_info.CO);
      for (int i = 0; i < behaviors_cnt; i++) {
        printf(" %s", behavior_str[behaviors[i]]);
      }
      puts("");
    }
    for (int i = 0; i < behaviors_cnt; i++) {
      behavior_result_cnt[behaviors[i]]++;
    }
  }
  printSummary(behavior_result_cnt[CACHE_BEHAVIOR_HIT],
               behavior_result_cnt[CACHE_BEHAVIOR_MISS],
               behavior_result_cnt[CACHE_BEHAVIOR_EVICTION]);
}

int main(int argc, char *argv[]) {
  char opt_ch;
  int verbose_mode;
  struct CacheInfo cache_info;
  char *trace_file;
  while ((opt_ch = getopt(argc, argv, "vE:s:b:t:")) != -1) {
    switch (opt_ch) {
      case 'v':verbose_mode = 1;
        break;
      case 's':cache_info.s = atoi(optarg);
        break;
      case 'E':cache_info.E = atoi(optarg);
        break;
      case 'b':cache_info.b = atoi(optarg);
        break;
      case 't':trace_file = optarg;
        break;
      default:printf("unknown opt ch %c\n", opt_ch);
        break;
    }
  }
  solove(cache_info, trace_file, verbose_mode);
  //printSummary(0, 0, 0);
  return 0;
}
