FROM ubuntu:20.04
RUN apt update && apt install -y locales \
	&& localedef -i en_US -c -f UTF-8 -A /usr/share/locale/locale.alias en_US.UTF-8
ENV LANG en_US.utf8
RUN apt install -y gcc-8-powerpc-linux-gnu binutils-multiarch build-essential
RUN addgroup --gid 1000 theuser
RUN adduser --disabled-password --gecos "" --force-badname --gid 1000 --uid 1000 theuser
USER theuser
WORKDIR /build
ENTRYPOINT ["make"]
