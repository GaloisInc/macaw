To build the binaries in this directory with the Docker container, run:

```
docker build . -t ppc32-cross
docker run -v $(pwd):/build --rm ppc32-cross
```
