// The number of user-space instructions that the calling thread retired, by a hardware counter of
// `perf_event_open`. The counter opens on the first call. The result is 0 if the kernel refuses it.
#include <lean/lean.h>
#include <linux/perf_event.h>
#include <string.h>
#include <sys/syscall.h>
#include <unistd.h>

static int counter_fd = -1;

static int open_counter(void) {
  struct perf_event_attr attr;
  memset(&attr, 0, sizeof attr);
  attr.type = PERF_TYPE_HARDWARE;
  attr.size = sizeof attr;
  attr.config = PERF_COUNT_HW_INSTRUCTIONS;
  attr.exclude_kernel = 1;
  attr.exclude_hv = 1;
  return (int)syscall(SYS_perf_event_open, &attr, 0, -1, -1, 0);
}

LEAN_EXPORT lean_obj_res distill_bench_instructions(lean_obj_arg world) {
  if (counter_fd < 0) counter_fd = open_counter();
  uint64_t count = 0;
  if (counter_fd < 0 || read(counter_fd, &count, sizeof count) != sizeof count) count = 0;
  return lean_io_result_mk_ok(lean_box_uint64(count));
}
