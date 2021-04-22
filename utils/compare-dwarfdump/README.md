# compare-dwarfdump

This contains a utility that extracts debug and frame information from
an Elf file and compares with output from `llvm-dwarfdump`.

## Usage

Run `compare-dwarfdump` with the names of any executable files or
directories to check.  Directories are checked recursively
automatically.  Symbolic links in directories are not followed.

If any inconsistencies are found, `compare-dwarfdump` will return
the output of LLVM's dwarfdump and Macaw's in `lldd` and `mcdd`
in the current directory.