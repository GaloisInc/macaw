To build the binaries in this directory with the Docker container, run:

```
docker build . -t ppc64-cross
docker run -v $(pwd):/build --rm ppc64-cross
```
