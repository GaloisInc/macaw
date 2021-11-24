# Revision history for macaw-arm

## Next

### Features

- Added support for symbolically executing system calls

### Breaking Changes

- The architecture-specific terminator and functions have changed to support system calls

  The terminators are gone, replaced by additional function forms. Note that these are compiled away during the translation into crucible.

