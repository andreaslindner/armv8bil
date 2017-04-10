FROM ubuntu:12.04.5

RUN apt-get update && apt-get install -y openssh-server inetutils-ping nano make
RUN apt-get update && apt-get install -y ocaml ocaml-native-compilers ocaml-findlib camlidl binutils-dev automake libcamomile-ocaml-dev otags libpcre3-dev camlp4-extra bison flex zlib1g-dev libgmp3-dev g++ libtool
RUN apt-get update && apt-get install -y gcc-multilib g++-multilib lib32z1-dev
RUN cd /root && wget https://github.com/0day1day/bap/archive/bap-0.7.tar.gz && tar -xzf bap-0.7.tar.gz
RUN cd /root/bap-bap-0.7 && ./autogen.sh && ./configure && make
RUN mkdir /var/run/sshd
RUN echo 'root:screencast' | chpasswd
RUN sed -i 's/PermitRootLogin prohibit-password/PermitRootLogin yes/' /etc/ssh/sshd_config

# SSH login fix. Otherwise user is kicked off after login
RUN sed 's@session\s*required\s*pam_loginuid.so@session optional pam_loginuid.so@g' -i /etc/pam.d/sshd

ENV NOTVISIBLE "in users profile"
RUN echo "export VISIBLE=now" >> /etc/profile

EXPOSE 22
CMD ["/usr/sbin/sshd", "-D"]

