// start of scheduler.h

// First, the API that the generated code will access.  In principle,
// we could then compile the scheduler separately and link an object
// file with the generated code.  In practice, we will embed all of
// this in the generated code.

// Scheduler handle.
struct scheduler;

// Initialise a scheduler (and start worker threads).
static int scheduler_init(struct scheduler *scheduler,
                          int num_workers,
                          double kappa);

// Shut down a scheduler (and destroy worker threads).
static int scheduler_destroy(struct scheduler *scheduler);

// Figure out the smallest amount of work that amortises task
// creation.
static int determine_kappa(double *kappa);

// How a segop should be scheduled.
enum scheduling {
  DYNAMIC,
  STATIC
};

// How a given task should be executed.  Filled out by the scheduler
// and passed to the segop function
struct scheduler_info {
  int64_t iter_pr_subtask;
  int64_t remainder;
  int nsubtasks;
  enum scheduling sched;
  int wake_up_threads;

  int64_t *task_time;
  int64_t *task_iter;
};

// A segop function.  This is what you hand the scheduler for
// execution.
typedef int (*segop_fn)(void* args,
                        int64_t iterations,
                        int tid,
                        struct scheduler_info info);

// A task for the scheduler to execute.
struct scheduler_segop {
  void *args;
  segop_fn top_level_fn;
  segop_fn nested_fn;
  int64_t iterations;
  enum scheduling sched;

  // Pointers to timer and iter associated with the task
  int64_t *task_time;
  int64_t *task_iter;

  // For debugging
  const char* name;
};

static inline int scheduler_prepare_task(struct scheduler *scheduler,
                                         struct scheduler_segop *task);

typedef int (*parloop_fn)(void* args,
                          int64_t start,
                          int64_t end,
                          int subtask_id,
                          int tid);

// A parallel parloop task.
struct scheduler_parloop {
  void* args;
  parloop_fn fn;
  int64_t iterations;
  struct scheduler_info info;

  // For debugging
  const char* name;
};

static inline int scheduler_execute_task(struct scheduler *scheduler,
                                         struct scheduler_parloop *task);

// Then the API implementation.

#include <signal.h>

#if defined(_WIN32)
#include <windows.h>
#elif defined(__APPLE__)
#include <sys/sysctl.h>
// For getting cpu usage of threads
#include <mach/mach.h>
#include <sys/resource.h>
#elif defined(__linux__)
#include <sys/sysinfo.h>
#include <sys/resource.h>
#include <signal.h>
#elif defined(__EMSCRIPTEN__)
#include <emscripten/threading.h>
#include <sys/sysinfo.h>
#include <sys/resource.h>
#include <signal.h>
#endif

/* Multicore Utility functions */

/* A wrapper for getting rusage on Linux and MacOS */
/* TODO maybe figure out this for windows */
static inline int getrusage_thread(struct rusage *rusage)
{
  int err = -1;
#if  defined(__APPLE__)
    thread_basic_info_data_t info = { 0 };
    mach_msg_type_number_t info_count = THREAD_BASIC_INFO_COUNT;
    kern_return_t kern_err;

    kern_err = thread_info(mach_thread_self(),
                           THREAD_BASIC_INFO,
                           (thread_info_t)&info,
                           &info_count);
    if (kern_err == KERN_SUCCESS) {
        memset(rusage, 0, sizeof(struct rusage));
        rusage->ru_utime.tv_sec = info.user_time.seconds;
        rusage->ru_utime.tv_usec = info.user_time.microseconds;
        rusage->ru_stime.tv_sec = info.system_time.seconds;
        rusage->ru_stime.tv_usec = info.system_time.microseconds;
        err = 0;
    } else {
        errno = EINVAL;
    }
#elif defined(__linux__) || __EMSCRIPTEN__
    err = getrusage(RUSAGE_THREAD, rusage);
#endif
    return err;
}

/* returns the number of logical cores */
static int num_processors()
{
#if  defined(_WIN32)
/* https://docs.microsoft.com/en-us/windows/win32/api/sysinfoapi/ns-sysinfoapi-system_info */
    SYSTEM_INFO sysinfo;
    GetSystemInfo(&sysinfo);
    int ncores = sysinfo.dwNumberOfProcessors;
    fprintf(stderr, "Found %d cores on your Windows machine\n Is that correct?\n", ncores);
    return ncores;
#elif defined(__APPLE__)
    int ncores;
    size_t ncores_size = sizeof(ncores);
    CHECK_ERRNO(sysctlbyname("hw.logicalcpu", &ncores, &ncores_size, NULL, 0),
                "sysctlbyname (hw.logicalcpu)");
    return ncores;
#elif defined(__linux__)
  return get_nprocs();
#elif __EMSCRIPTEN__
  return emscripten_num_logical_cores();
#else
  fprintf(stderr, "operating system not recognised\n");
  return -1;
#endif
}

static unsigned int g_seed;

// Used to seed the generator.
static inline void fast_srand(unsigned int seed) {
    g_seed = seed;
}

// Compute a pseudorandom integer.
// Output value in range [0, 32767]
static inline unsigned int fast_rand(void) {
    g_seed = (214013*g_seed+2531011);
    return (g_seed>>16)&0x7FFF;
}

struct subtask_queue {
  int capacity;             // Size of the buffer.
  int first;                // Index of the start of the ring buffer.
  int num_used;             // Number of used elements in the buffer.
  struct subtask **buffer;

  pthread_mutex_t mutex;    // Mutex used for synchronisation.
  pthread_cond_t cond;      // Condition variable used for synchronisation.
  int dead;

#if defined(MCPROFILE)
  /* Profiling fields */
  uint64_t time_enqueue;
  uint64_t time_dequeue;
  uint64_t n_dequeues;
  uint64_t n_enqueues;
#endif
};

/* A subtask that can be executed by a worker */
struct subtask {
  /* The parloop function */
  parloop_fn fn;
  /* Execution parameters */
  void* args;
  int64_t start, end;
  int id;

  /* Dynamic scheduling parameters */
  int chunkable;
  int64_t chunk_size;

  /* Shared variables across subtasks */
  volatile int *counter; // Counter for ongoing subtasks
  // Shared task timers and iterators
  int64_t *task_time;
  int64_t *task_iter;

  /* For debugging */
  const char *name;
};


struct worker {
  pthread_t thread;
  struct scheduler *scheduler;  /* Reference to the scheduler struct the worker belongs to*/
  struct subtask_queue q;
  int dead;
  int tid;                      /* Just a thread id */

  /* "thread local" time fields used for online algorithm */
  uint64_t timer;
  uint64_t total;
  int nested; /* How nested the current computation is */

  // Profiling fields
  int output_usage;            /* Whether to dump thread usage */
  uint64_t time_spent_working; /* Time spent in parloop functions */
};

static inline void output_worker_usage(struct worker *worker)
{
  struct rusage usage;
  CHECK_ERRNO(getrusage_thread(&usage), "getrusage_thread");
  struct timeval user_cpu_time = usage.ru_utime;
  struct timeval sys_cpu_time = usage.ru_stime;
  fprintf(stderr, "tid: %2d - work time %10llu us - user time: %10llu us - sys: %10llu us\n",
          worker->tid,
          (long long unsigned)worker->time_spent_working / 1000,
          (long long unsigned)(user_cpu_time.tv_sec * 1000000 + user_cpu_time.tv_usec),
          (long long unsigned)(sys_cpu_time.tv_sec * 1000000 + sys_cpu_time.tv_usec));
}

/* Doubles the size of the queue */
static inline int subtask_queue_grow_queue(struct subtask_queue *subtask_queue) {

  int new_capacity = 2 * subtask_queue->capacity;
#ifdef MCDEBUG
  fprintf(stderr, "Growing queue to %d\n", subtask_queue->capacity * 2);
#endif

  struct subtask **new_buffer = calloc(new_capacity, sizeof(struct subtask*));
  for (int i = 0; i < subtask_queue->num_used; i++) {
    new_buffer[i] = subtask_queue->buffer[(subtask_queue->first + i) % subtask_queue->capacity];
  }

  free(subtask_queue->buffer);
  subtask_queue->buffer = new_buffer;
  subtask_queue->capacity = new_capacity;
  subtask_queue->first = 0;

  return 0;
}

// Initialise a job queue with the given capacity.  The queue starts out
// empty.  Returns non-zero on error.
static inline int subtask_queue_init(struct subtask_queue *subtask_queue, int capacity)
{
  assert(subtask_queue != NULL);
  memset(subtask_queue, 0, sizeof(struct subtask_queue));

  subtask_queue->capacity = capacity;
  subtask_queue->buffer = calloc(capacity, sizeof(struct subtask*));
  if (subtask_queue->buffer == NULL) {
    return -1;
  }

  CHECK_ERRNO(pthread_mutex_init(&subtask_queue->mutex, NULL), "pthread_mutex_init");
  CHECK_ERRNO(pthread_cond_init(&subtask_queue->cond, NULL), "pthread_cond_init");

  return 0;
}

// Destroy the job queue.  Blocks until the queue is empty before it
// is destroyed.
static inline int subtask_queue_destroy(struct subtask_queue *subtask_queue)
{
  assert(subtask_queue != NULL);

  CHECK_ERR(pthread_mutex_lock(&subtask_queue->mutex), "pthread_mutex_lock");

  while (subtask_queue->num_used != 0) {
    CHECK_ERR(pthread_cond_wait(&subtask_queue->cond, &subtask_queue->mutex), "pthread_cond_wait");
  }

  // Queue is now empty.  Let's kill it!
  subtask_queue->dead = 1;
  free(subtask_queue->buffer);
  CHECK_ERR(pthread_cond_broadcast(&subtask_queue->cond), "pthread_cond_broadcast");
  CHECK_ERR(pthread_mutex_unlock(&subtask_queue->mutex), "pthread_mutex_unlock");

  return 0;
}

static inline void dump_queue(struct worker *worker)
{
  struct subtask_queue *subtask_queue = &worker->q;
  CHECK_ERR(pthread_mutex_lock(&subtask_queue->mutex), "pthread_mutex_lock");
  for (int i = 0; i < subtask_queue->num_used; i++) {
    struct subtask * subtask = subtask_queue->buffer[(subtask_queue->first + i) % subtask_queue->capacity];
    printf("queue tid %d with %d task %s\n", worker->tid, i, subtask->name);
  }
  CHECK_ERR(pthread_cond_broadcast(&subtask_queue->cond), "pthread_cond_broadcast");
  CHECK_ERR(pthread_mutex_unlock(&subtask_queue->mutex), "pthread_mutex_unlock");
}

// Push an element onto the end of the job queue.  Blocks if the
// subtask_queue is full (its size is equal to its capacity).  Returns
// non-zero on error.  It is an error to push a job onto a queue that
// has been destroyed.
static inline int subtask_queue_enqueue(struct worker *worker, struct subtask *subtask )
{
  assert(worker != NULL);
  struct subtask_queue *subtask_queue = &worker->q;

#ifdef MCPROFILE
  uint64_t start = get_wall_time();
#endif

  CHECK_ERR(pthread_mutex_lock(&subtask_queue->mutex), "pthread_mutex_lock");
  // Wait until there is room in the subtask_queue.
  while (subtask_queue->num_used == subtask_queue->capacity && !subtask_queue->dead) {
    if (subtask_queue->num_used == subtask_queue->capacity) {
      CHECK_ERR(subtask_queue_grow_queue(subtask_queue), "subtask_queue_grow_queue");
      continue;
    }
    CHECK_ERR(pthread_cond_wait(&subtask_queue->cond, &subtask_queue->mutex), "pthread_cond_wait");
  }

  if (subtask_queue->dead) {
    CHECK_ERR(pthread_mutex_unlock(&subtask_queue->mutex), "pthread_mutex_unlock");
    return -1;
  }

  // If we made it past the loop, there is room in the subtask_queue.
  subtask_queue->buffer[(subtask_queue->first + subtask_queue->num_used) % subtask_queue->capacity] = subtask;
  subtask_queue->num_used++;

#ifdef MCPROFILE
  uint64_t end = get_wall_time();
  subtask_queue->time_enqueue += (end - start);
  subtask_queue->n_enqueues++;
#endif
  // Broadcast a reader (if any) that there is now an element.
  CHECK_ERR(pthread_cond_broadcast(&subtask_queue->cond), "pthread_cond_broadcast");
  CHECK_ERR(pthread_mutex_unlock(&subtask_queue->mutex), "pthread_mutex_unlock");

  return 0;
}


/* Like subtask_queue_dequeue, but with two differences:
   1) the subtask is stolen from the __front__ of the queue
   2) returns immediately if there is no subtasks queued,
      as we dont' want to block on another workers queue and
*/
static inline int subtask_queue_steal(struct worker *worker,
                                      struct subtask **subtask)
{
  struct subtask_queue *subtask_queue = &worker->q;
  assert(subtask_queue != NULL);

#ifdef MCPROFILE
  uint64_t start = get_wall_time();
#endif
  CHECK_ERR(pthread_mutex_lock(&subtask_queue->mutex), "pthread_mutex_lock");

  if (subtask_queue->num_used == 0) {
    CHECK_ERR(pthread_cond_broadcast(&subtask_queue->cond), "pthread_cond_broadcast");
    CHECK_ERR(pthread_mutex_unlock(&subtask_queue->mutex), "pthread_mutex_unlock");
    return 1;
  }

  if (subtask_queue->dead) {
    CHECK_ERR(pthread_mutex_unlock(&subtask_queue->mutex), "pthread_mutex_unlock");
    return -1;
  }

  // Tasks gets stolen from the "front"
  struct subtask *cur_back = subtask_queue->buffer[subtask_queue->first];
  struct subtask *new_subtask = NULL;
  int remaining_iter = cur_back->end - cur_back->start;
  // If subtask is chunkable, we steal half of the iterations
  if (cur_back->chunkable && remaining_iter > 1) {
      int64_t half = remaining_iter / 2;
      new_subtask = malloc(sizeof(struct subtask));
      *new_subtask = *cur_back;
      new_subtask->start = cur_back->end - half;
      cur_back->end = new_subtask->start;
      __atomic_fetch_add(cur_back->counter, 1, __ATOMIC_RELAXED);
  } else {
    new_subtask = cur_back;
    subtask_queue->num_used--;
    subtask_queue->first = (subtask_queue->first + 1) % subtask_queue->capacity;
  }
  *subtask = new_subtask;

  if (*subtask == NULL) {
    CHECK_ERR(pthread_mutex_unlock(&subtask_queue->mutex), "pthred_mutex_unlock");
    return 1;
  }

#ifdef MCPROFILE
  uint64_t end = get_wall_time();
  subtask_queue->time_dequeue += (end - start);
  subtask_queue->n_dequeues++;
#endif

  // Broadcast a writer (if any) that there is now room for more.
  CHECK_ERR(pthread_cond_broadcast(&subtask_queue->cond), "pthread_cond_broadcast");
  CHECK_ERR(pthread_mutex_unlock(&subtask_queue->mutex), "pthread_mutex_unlock");

  return 0;
}


// Pop an element from the back of the job queue.
// Optional argument can be provided to block or not
static inline int subtask_queue_dequeue(struct worker *worker,
                                        struct subtask **subtask, int blocking)
{
  assert(worker != NULL);
  struct subtask_queue *subtask_queue = &worker->q;

#ifdef MCPROFILE
  uint64_t start = get_wall_time();
#endif

  CHECK_ERR(pthread_mutex_lock(&subtask_queue->mutex), "pthread_mutex_lock");
  if (subtask_queue->num_used == 0 && !blocking) {
    CHECK_ERR(pthread_mutex_unlock(&subtask_queue->mutex), "pthread_mutex_unlock");
    return 1;
  }
  // Try to steal some work while the subtask_queue is empty
  while (subtask_queue->num_used == 0 && !subtask_queue->dead) {
    pthread_cond_wait(&subtask_queue->cond, &subtask_queue->mutex);
  }

  if (subtask_queue->dead) {
    CHECK_ERR(pthread_mutex_unlock(&subtask_queue->mutex), "pthread_mutex_unlock");
    return -1;
  }

  // dequeue pops from the back
  *subtask = subtask_queue->buffer[(subtask_queue->first + subtask_queue->num_used - 1) % subtask_queue->capacity];
  subtask_queue->num_used--;

  if (*subtask == NULL) {
    assert(!"got NULL ptr");
    CHECK_ERR(pthread_mutex_unlock(&subtask_queue->mutex), "pthred_mutex_unlock");
    return -1;
  }

#ifdef MCPROFILE
  uint64_t end = get_wall_time();
  subtask_queue->time_dequeue += (end - start);
  subtask_queue->n_dequeues++;
#endif

  // Broadcast a writer (if any) that there is now room for more.
  CHECK_ERR(pthread_cond_broadcast(&subtask_queue->cond), "pthread_cond_broadcast");
  CHECK_ERR(pthread_mutex_unlock(&subtask_queue->mutex), "pthread_mutex_unlock");

  return 0;
}

static inline int subtask_queue_is_empty(struct subtask_queue *subtask_queue)
{
  return subtask_queue->num_used == 0;
}

/* Scheduler definitions */

struct scheduler {
  struct worker *workers;
  int num_threads;

  // If there is work to steal => active_work > 0
  volatile int active_work;

  // Only one error can be returned at the time now.  Maybe we can
  // provide a stack like structure for pushing errors onto if we wish
  // to backpropagte multiple errors
  volatile int error;

  // kappa time unit in nanoseconds
  double kappa;
};


// Thread local variable worker struct
// Note that, accesses to tls variables are expensive
// Minimize direct references to this variable
__thread struct worker* worker_local = NULL;

static int64_t total_now(int64_t total, int64_t time) {
  return total + (get_wall_time_ns() - time);
}

static int random_other_worker(struct scheduler *scheduler, int my_id) {
  int my_num_workers = scheduler->num_threads;
  assert(my_num_workers != 1);
  int i = fast_rand() % (my_num_workers - 1);
  if (i >= my_id) {
    i++;
  }
#ifdef MCDEBUG
  assert(i >= 0);
  assert(i < my_num_workers);
  assert(i != my_id);
#endif

  return i;
}


static inline int64_t compute_chunk_size(double kappa, struct subtask* subtask)
{
  double C = (double)*subtask->task_time / (double)*subtask->task_iter;
  if (C == 0.0F) C += DBL_EPSILON;
  return smax64((int64_t)(kappa / C), 1);
}

/* Takes a chunk from subtask and enqueues the remaining iterations onto the worker's queue */
/* A no-op if the subtask is not chunkable */
static inline struct subtask* chunk_subtask(struct worker* worker, struct subtask *subtask)
{
  if (subtask->chunkable) {
    // Do we have information from previous runs avaliable
    if (*subtask->task_iter > 0) {
      subtask->chunk_size = compute_chunk_size(worker->scheduler->kappa, subtask);
      assert(subtask->chunk_size > 0);
    }
    int64_t remaining_iter = subtask->end - subtask->start;
    assert(remaining_iter > 0);
    if (remaining_iter > subtask->chunk_size) {
      struct subtask *new_subtask = malloc(sizeof(struct subtask));
      *new_subtask = *subtask;
      // increment the subtask join counter to account for new subtask
      __atomic_fetch_add(subtask->counter, 1, __ATOMIC_RELAXED);
      // Update range parameters
      subtask->end = subtask->start + subtask->chunk_size;
      new_subtask->start = subtask->end;
      subtask_queue_enqueue(worker, new_subtask);
    }
  }
  return subtask;
}

static inline int run_subtask(struct worker* worker, struct subtask* subtask)
{
  assert(subtask != NULL);
  assert(worker != NULL);

  subtask = chunk_subtask(worker, subtask);
  worker->total = 0;
  worker->timer = get_wall_time_ns();
#if defined(MCPROFILE)
  int64_t start = worker->timer;
#endif
  worker->nested++;
  int err = subtask->fn(subtask->args, subtask->start, subtask->end,
                        subtask->chunkable ? worker->tid : subtask->id,
                        worker->tid);
  worker->nested--;
  // Some error occured during some other subtask
  // so we just clean-up and return
  if (worker->scheduler->error != 0) {
    // Even a failed task counts as finished.
    __atomic_fetch_sub(subtask->counter, 1, __ATOMIC_RELAXED);
    free(subtask);
    return 0;
  }
  if (err != 0) {
    __atomic_store_n(&worker->scheduler->error, err, __ATOMIC_RELAXED);
  }
  // Total sequential time spent
  int64_t time_elapsed = total_now(worker->total, worker->timer);
#if defined(MCPROFILE)
  worker->time_spent_working += get_wall_time_ns() - start;
#endif
  int64_t iter = subtask->end - subtask->start;
  // report measurements
  // These updates should really be done using a single atomic CAS operation
  __atomic_fetch_add(subtask->task_time, time_elapsed, __ATOMIC_RELAXED);
  __atomic_fetch_add(subtask->task_iter, iter, __ATOMIC_RELAXED);
  // We need a fence here, since if the counter is decremented before either
  // of the two above are updated bad things can happen, e.g. if they are stack-allocated
  __atomic_thread_fence(__ATOMIC_SEQ_CST);
  __atomic_fetch_sub(subtask->counter, 1, __ATOMIC_RELAXED);
  free(subtask);
  return 0;
}


static inline int is_small(struct scheduler_segop *task, struct scheduler *scheduler, int *nsubtasks)
{
  int64_t time = *task->task_time;
  int64_t iter = *task->task_iter;

  if (task->sched == DYNAMIC || iter == 0) {
    *nsubtasks = scheduler->num_threads;
    return 0;
  }

  // Estimate the constant C
  double C = (double)time / (double)iter;
  double cur_task_iter = (double) task->iterations;

  // Returns true if the task is small i.e.
  // if the number of iterations times C is smaller
  // than the overhead of subtask creation
  if (C == 0.0F || C * cur_task_iter < scheduler->kappa) {
    *nsubtasks = 1;
    return 1;
  }

  // Else compute how many subtasks this tasks should create
  int64_t min_iter_pr_subtask = smax64(scheduler->kappa / C, 1);
  *nsubtasks = smin64(smax64(task->iterations / min_iter_pr_subtask, 1), scheduler->num_threads);

  return 0;
}

// TODO make this prettier
static inline struct subtask* create_subtask(parloop_fn fn,
                                             void* args,
                                             const char* name,
                                             volatile int* counter,
                                             int64_t *timer,
                                             int64_t *iter,
                                             int64_t start, int64_t end,
                                             int chunkable,
                                             int64_t chunk_size,
                                             int id)
{
  struct subtask* subtask = malloc(sizeof(struct subtask));
  if (subtask == NULL) {
    assert(!"malloc failed in create_subtask");
    return NULL;
  }
  subtask->fn         = fn;
  subtask->args       = args;

  subtask->counter    = counter;
  subtask->task_time  = timer;
  subtask->task_iter  = iter;

  subtask->start      = start;
  subtask->end        = end;
  subtask->id         = id;
  subtask->chunkable  = chunkable;
  subtask->chunk_size = chunk_size;

  subtask->name       = name;
  return subtask;
}

static int dummy_counter = 0;
static int64_t dummy_timer = 0;
static int64_t dummy_iter = 0;

static int dummy_fn(void *args, int64_t start, int64_t end, int subtask_id, int tid) {
  (void)args;
  (void)start;
  (void)end;
  (void)subtask_id;
  (void)tid;
  return 0;
}

// Wake up threads, who are blocking by pushing a dummy task
// onto their queue
static inline void wake_up_threads(struct scheduler *scheduler, int start_tid, int end_tid) {

#if defined(MCDEBUG)
  assert(start_tid >= 1);
  assert(end_tid <= scheduler->num_threads);
#endif
  for (int i = start_tid; i < end_tid; i++) {
    struct subtask *subtask = create_subtask(dummy_fn, NULL, "dummy_fn",
                                            &dummy_counter,
                                            &dummy_timer, &dummy_iter,
                                            0, 0,
                                            0, 0,
                                            0);
    CHECK_ERR(subtask_queue_enqueue(&scheduler->workers[i], subtask), "subtask_queue_enqueue");
  }
}

static inline int is_finished(struct worker *worker) {
  return worker->dead && subtask_queue_is_empty(&worker->q);
}

// Try to steal from a random queue
static inline int steal_from_random_worker(struct worker* worker)
{
  int my_id = worker->tid;
  struct scheduler* scheduler = worker->scheduler;
  int k = random_other_worker(scheduler, my_id);
  struct worker *worker_k = &scheduler->workers[k];
  struct subtask* subtask =  NULL;
  int retval = subtask_queue_steal(worker_k, &subtask);
  if (retval == 0) {
    subtask_queue_enqueue(worker, subtask);
    return 1;
  }
  return 0;
}


static inline void *scheduler_worker(void* args)
{
  struct worker *worker = (struct worker*) args;
  struct scheduler *scheduler = worker->scheduler;
  worker_local = worker;
  struct subtask *subtask = NULL;

  while(!is_finished(worker)) {
    if (!subtask_queue_is_empty(&worker->q)) {
      int retval = subtask_queue_dequeue(worker, &subtask, 0);
      if (retval == 0) {
        assert(subtask != NULL);
        CHECK_ERR(run_subtask(worker, subtask), "run_subtask");
      } // else someone stole our work

    } else if (scheduler->active_work) { /* steal */
      while (!is_finished(worker) && scheduler->active_work) {
        if (steal_from_random_worker(worker)) {
          break;
        }
      }
    } else { /* go back to sleep and wait for work */
      int retval = subtask_queue_dequeue(worker, &subtask, 1);
      if (retval == 0) {
        assert(subtask != NULL);
        CHECK_ERR(run_subtask(worker, subtask), "run_subtask");
      }
    }
  }

  assert(subtask_queue_is_empty(&worker->q));
#if defined(MCPROFILE)
  if (worker->output_usage)
    output_worker_usage(worker);
#endif
  return NULL;
}


static inline int scheduler_execute_parloop(struct scheduler *scheduler,
                                            struct scheduler_parloop *task,
                                            int64_t *timer)
{

  struct worker *worker = worker_local;

  struct scheduler_info info = task->info;
  int64_t iter_pr_subtask = info.iter_pr_subtask;
  int64_t remainder = info.remainder;
  int nsubtasks = info.nsubtasks;
  volatile int join_counter = nsubtasks;

  // Shared timer used to sum up all
  // sequential work from each subtask
  int64_t task_timer = 0;
  int64_t task_iter = 0;

  enum scheduling sched = info.sched;
  /* If each subtasks should be processed in chunks */
  int chunkable = sched == STATIC ? 0 : 1;
  int64_t chunk_size = 1; // The initial chunk size when no info is avaliable


  if (info.wake_up_threads || sched == DYNAMIC)
    __atomic_add_fetch(&scheduler->active_work, nsubtasks, __ATOMIC_RELAXED);

  int64_t start = 0;
  int64_t end = iter_pr_subtask + (int64_t)(remainder != 0);
  for (int subtask_id = 0; subtask_id < nsubtasks; subtask_id++) {
    struct subtask *subtask = create_subtask(task->fn, task->args, task->name,
                                              &join_counter,
                                              &task_timer, &task_iter,
                                              start, end,
                                              chunkable, chunk_size,
                                              subtask_id);
    assert(subtask != NULL);
    // In most cases we will never have more subtasks than workers,
    // but there can be exceptions (e.g. the kappa tuning function).
    struct worker *subtask_worker =
      worker->nested
      ? &scheduler->workers[worker->tid]
      : &scheduler->workers[subtask_id % scheduler->num_threads];
    CHECK_ERR(subtask_queue_enqueue(subtask_worker, subtask),
              "subtask_queue_enqueue");
    // Update range params
    start = end;
    end += iter_pr_subtask + ((subtask_id + 1) < remainder);
  }

  if (info.wake_up_threads) {
    wake_up_threads(scheduler, nsubtasks, scheduler->num_threads);
  }

  // Join (wait for subtasks to finish)
  while(join_counter != 0) {
    if (!subtask_queue_is_empty(&worker->q)) {
      struct subtask *subtask = NULL;
      int err = subtask_queue_dequeue(worker, &subtask, 0);
      if (err == 0 ) {
        CHECK_ERR(run_subtask(worker, subtask), "run_subtask");
      }
    } else {
      if (steal_from_random_worker(worker)) {
        struct subtask *subtask = NULL;
        int err = subtask_queue_dequeue(worker, &subtask, 0);
        if (err == 0) {
          CHECK_ERR(run_subtask(worker, subtask), "run_subtask");
        }
      }
    }
  }


  if (info.wake_up_threads || sched == DYNAMIC) {
    __atomic_sub_fetch(&scheduler->active_work, nsubtasks, __ATOMIC_RELAXED);
  }

  // Write back timing results of all sequential work
  (*timer) += task_timer;
  return scheduler->error;
}


static inline int scheduler_execute_task(struct scheduler *scheduler,
                                         struct scheduler_parloop *task)
{

  struct worker *worker = worker_local;

  int err = 0;

  // How much sequential work was performed by the task
  int64_t task_timer = 0;

  /* Execute task sequential or parallel based on decision made earlier */
  if (task->info.nsubtasks == 1) {
    int64_t start = get_wall_time_ns();
    err = task->fn(task->args, 0, task->iterations, 0, worker->tid);
    int64_t end = get_wall_time_ns();
    task_timer = end - start;
    worker->time_spent_working += task_timer;
    // Report time measurements
    // TODO the update of both of these should really be a single atomic!!
    __atomic_fetch_add(task->info.task_time, task_timer, __ATOMIC_RELAXED);
    __atomic_fetch_add(task->info.task_iter, task->iterations, __ATOMIC_RELAXED);
  } else {
    // Add "before" time if we already are inside a task
    int64_t time_before = 0;
    if (worker->nested > 0) {
      time_before = total_now(worker->total, worker->timer);
    }

    err = scheduler_execute_parloop(scheduler, task, &task_timer);

    // Report time measurements
    // TODO the update of both of these should really be a single atomic!!
    __atomic_fetch_add(task->info.task_time, task_timer, __ATOMIC_RELAXED);
    __atomic_fetch_add(task->info.task_iter, task->iterations, __ATOMIC_RELAXED);

    // Update timers to account for new timings
    worker->total = time_before + task_timer;
    worker->timer = get_wall_time_ns();
  }


  return err;
}

/* Decide on how schedule the incoming task i.e. how many subtasks and
   to run sequential or (potentially nested) parallel code body */
static inline int scheduler_prepare_task(struct scheduler* scheduler,
                                         struct scheduler_segop *task)
{
  assert(task != NULL);

  struct worker *worker = worker_local;
  struct scheduler_info info;
  info.task_time = task->task_time;
  info.task_iter = task->task_iter;

  int nsubtasks;
  // Decide if task should be scheduled sequentially
  if (is_small(task, scheduler, &nsubtasks)) {
    info.iter_pr_subtask = task->iterations;
    info.remainder = 0;
    info.nsubtasks = nsubtasks;
    return task->top_level_fn(task->args, task->iterations, worker->tid, info);
  } else {
    info.iter_pr_subtask = task->iterations / nsubtasks;
    info.remainder = task->iterations % nsubtasks;
    info.sched = task->sched;
    switch (task->sched) {
    case STATIC:
      info.nsubtasks = info.iter_pr_subtask == 0 ? info.remainder : ((task->iterations - info.remainder) / info.iter_pr_subtask);
      break;
    case DYNAMIC:
      // As any thread can take any subtasks, we are being safe with using
      // an upper bound on the number of tasks such that the task allocate enough memory
      info.nsubtasks = info.iter_pr_subtask == 0 ? info.remainder : nsubtasks;
      break;
    default:
      assert(!"Got unknown scheduling");
    }
  }

  info.wake_up_threads = 0;
  // We only use the nested parallel segop function if we can't exchaust all cores
  // using the outer most level
  if (task->nested_fn != NULL && info.nsubtasks < scheduler->num_threads && info.nsubtasks == task->iterations) {
    if (worker->nested == 0)
      info.wake_up_threads = 1;
    return task->nested_fn(task->args, task->iterations, worker->tid, info);
  }

  return task->top_level_fn(task->args, task->iterations, worker->tid, info);
}

// Now some code for finding the proper value of kappa on a given
// machine (the smallest amount of work that amortises the cost of
// task creation).

struct tuning_struct {
  int32_t *free_tuning_res;
  int32_t *array;
};

// Reduction function over an integer array
static int tuning_loop(void *args, int64_t start, int64_t end,
                                     int flat_tid, int tid) {
  (void)flat_tid;
  (void)tid;

  int err = 0;
  struct tuning_struct *tuning_struct = (struct tuning_struct *) args;
  int32_t *array = tuning_struct->array;
  int32_t *tuning_res = tuning_struct->free_tuning_res;

  int32_t sum = 0;
  for (int i = start; i < end; i++) {
    int32_t y = array[i];
    sum = add32(sum, y);
  }
  *tuning_res = sum;
  return err;
}

// The main entry point for the tuning process.  Sets the provided
// variable ``kappa``.
static int determine_kappa(double *kappa) {
  int err = 0;

  int64_t iterations = 100000000;
  int64_t tuning_time = 0;
  int64_t tuning_iter = 0;

  int32_t *array = malloc(sizeof(int32_t) * iterations);
  for (int64_t i = 0; i < iterations; i++) {
    array[i] = fast_rand();
  }

  int64_t start_tuning = get_wall_time_ns();
  /* **************************** */
  /* Run sequential reduce first' */
  /* **************************** */
  int64_t tuning_sequentiual_start = get_wall_time_ns();
  struct tuning_struct tuning_struct;
  int32_t tuning_res;
  tuning_struct.free_tuning_res = &tuning_res;
  tuning_struct.array = array;

  err = tuning_loop(&tuning_struct, 0, iterations, 0, 0);
  int64_t tuning_sequentiual_end = get_wall_time_ns();
  int64_t sequential_elapsed = tuning_sequentiual_end - tuning_sequentiual_start;

  double C = (double)sequential_elapsed / (double)iterations;
  fprintf(stderr, " Time for sequential run is %lld - Found C %f\n", (long long)sequential_elapsed, C);

  /* ********************** */
  /* Now run tuning process */
  /* ********************** */
  // Setup a scheduler with a single worker
  struct scheduler scheduler;
  scheduler.num_threads = 1;
  scheduler.workers = malloc(sizeof(struct worker));
  worker_local = &scheduler.workers[0];
  worker_local->tid = 0;
  CHECK_ERR(subtask_queue_init(&scheduler.workers[0].q, 1024),
            "failed to init queue for worker %d\n", 0);

  // Start tuning for kappa
  double kappa_tune = 1000; // Initial kappa is 1 us
  double ratio;
  int64_t time_elapsed;
  while(1) {
    int64_t min_iter_pr_subtask = (int64_t) (kappa_tune / C) == 0 ? 1 : (kappa_tune / C);
    int nsubtasks = iterations / min_iter_pr_subtask;
    struct scheduler_info info;
    info.iter_pr_subtask = min_iter_pr_subtask;

    info.nsubtasks = iterations / min_iter_pr_subtask;
    info.remainder = iterations % min_iter_pr_subtask;
    info.task_time = &tuning_time;
    info.task_iter = &tuning_iter;
    info.sched = STATIC;

    struct scheduler_parloop parloop;
    parloop.name = "tuning_loop";
    parloop.fn = tuning_loop;
    parloop.args = &tuning_struct;
    parloop.iterations = iterations;
    parloop.info = info;

    int64_t tuning_chunked_start = get_wall_time_ns();
    int determine_kappa_err =
      scheduler_execute_task(&scheduler,
                             &parloop);
    assert(determine_kappa_err == 0);
    int64_t tuning_chunked_end = get_wall_time_ns();
    time_elapsed =  tuning_chunked_end - tuning_chunked_start;

    ratio = (double)time_elapsed / (double)sequential_elapsed;
    if (ratio < 1.055) {
      break;
    }
    kappa_tune += 100; // Increase by 100 ns at the time
    fprintf(stderr, "nsubtask %d - kappa %f - ratio %f\n", nsubtasks, kappa_tune, ratio);
  }

  int64_t end_tuning = get_wall_time_ns();
  fprintf(stderr, "tuning took %lld ns and found kappa %f - time %lld - ratio %f\n",
          (long long)end_tuning - start_tuning,
          kappa_tune,
          (long long)time_elapsed,
          ratio);
  *kappa = kappa_tune;

  // Clean-up
  CHECK_ERR(subtask_queue_destroy(&scheduler.workers[0].q), "failed to destroy queue");
  free(array);
  free(scheduler.workers);
  return err;
}

static int scheduler_init(struct scheduler *scheduler,
                          int num_workers,
                          double kappa) {
  assert(num_workers > 0);

  scheduler->kappa = kappa;
  scheduler->num_threads = num_workers;
  scheduler->active_work = 0;
  scheduler->error = 0;

  scheduler->workers = calloc(num_workers, sizeof(struct worker));

  const int queue_capacity = 1024;

  worker_local = &scheduler->workers[0];
  worker_local->tid = 0;
  worker_local->scheduler = scheduler;
  CHECK_ERR(subtask_queue_init(&worker_local->q, queue_capacity),
            "failed to init queue for worker %d\n", 0);

  for (int i = 1; i < num_workers; i++) {
    struct worker *cur_worker = &scheduler->workers[i];
    memset(cur_worker, 0, sizeof(struct worker));
    cur_worker->tid = i;
    cur_worker->output_usage = 0;
    cur_worker->scheduler = scheduler;
    CHECK_ERR(subtask_queue_init(&cur_worker->q, queue_capacity),
              "failed to init queue for worker %d\n", i);

    CHECK_ERR(pthread_create(&cur_worker->thread,
                             NULL,
                             &scheduler_worker,
                             cur_worker),
              "Failed to create worker %d\n", i);
  }

  return 0;
}

static int scheduler_destroy(struct scheduler *scheduler) {
  // First mark them all as dead.
  for (int i = 1; i < scheduler->num_threads; i++) {
    struct worker *cur_worker = &scheduler->workers[i];
    cur_worker->dead = 1;
  }

  // Then destroy their task queues (this will wake up the threads and
  // make them do their shutdown).
  for (int i = 1; i < scheduler->num_threads; i++) {
    struct worker *cur_worker = &scheduler->workers[i];
    subtask_queue_destroy(&cur_worker->q);
  }

  // Then actually wait for them to stop.
  for (int i = 1; i < scheduler->num_threads; i++) {
    struct worker *cur_worker = &scheduler->workers[i];
    CHECK_ERR(pthread_join(scheduler->workers[i].thread, NULL), "pthread_join");
  }

  free(scheduler->workers);

  return 0;
}

// End of scheduler.h
