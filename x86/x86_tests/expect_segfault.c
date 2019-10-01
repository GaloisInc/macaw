#include "expect_segfault.h"
#include "utils.h"

#include <pthread.h>
#include <signal.h>
#include <string.h>





// Global to indicate segfault occured.

volatile sig_atomic_t segfault = 0;

// Set segfault and exit pthread.
static
void segfault_sigaction(int signal, siginfo_t *si, void *arg)
{
    segfault = 1;
    pthread_exit(0);
}

// A pair with test function and argument.
struct test_pair {
    test_fn fn;
    void* arg;
};

// pthread function for running user test case.
static
void* thread_fn(void* arg) {

    struct test_pair* s = (struct test_pair *) arg;


    struct sigaction sa;
    memset(&sa, 0, sizeof(struct sigaction));
    sigemptyset(&sa.sa_mask);
    sa.sa_sigaction = segfault_sigaction;
    sa.sa_flags   = SA_SIGINFO;

    struct sigaction oldsa;
    sigaction(SIGSEGV, &sa, &oldsa);

    s->fn(s->arg);

    sigaction(SIGSEGV, &oldsa, 0);

    return 0;
}

// Run a test case with given argument. that is expected to segfault.
void expect_segfault(test_fn test, void* arg, const char* testname) {
    pthread_t waiting_thread;
    segfault = 0;

    struct test_pair s;
    s.fn = test;
    s.arg = arg;

    int res = pthread_create(&waiting_thread, 0, &thread_fn, &s);
    if (res) {
        fprintf(stderr, "Thread creation failed\n");
    }


    void* status;
    res = pthread_join(waiting_thread, &status);
    if (res) {
        fprintf(stderr, "Waiting for termination failed\n");
    }

    my_assert(segfault, testname);
}
