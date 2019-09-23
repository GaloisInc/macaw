// Provides operation for testing a C function triggers a segfault.

// Function for user test case.
typedef void (*test_fn)(void*);


void expect_segfault(test_fn test, void* arg, const char* testname);
