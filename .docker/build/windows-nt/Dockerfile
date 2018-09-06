# vale build container

# Define on fstar-version.json what FStar base container image
# vale build should use.
# By default it always look for the latest FStar container available
# In case you would like to reference a specific commit,
# replace latest with the commit id from github using 12 characters.
# Latest can only be used with branch master,
# for any other branch please use the specific commit id on the config file.
ARG COMMITID
FROM fstar-windows-nt:${COMMITID}

ARG BUILDLOGFILE
ARG MAXTHREADS
ARG TARGET
ARG BRANCHNAME
ARG FSTARSOURCEVERSION

# Add ssh key
# We cannot copy directly to the .ssh folder, instead we copy to a temp folder
WORKDIR "everestsshkey"
COPY id_rsa .
WORKDIR ".."

# Now, using bash we copy the file, set the correct security and remove the previous folder
RUN Invoke-BashCmd '"cd .ssh && cp ../everestsshkey/id_rsa . && chmod 600 id_rsa && rm -rf ../everestsshkey"'

# Do some cleanup
RUN Invoke-BashCmd rm -rf FStar/hacl-star
RUN Invoke-BashCmd rm -rf FStar/hacl-star-old
RUN Invoke-BashCmd rm -rf FStar/kremlin
RUN Invoke-BashCmd rm -rf FStar/hacl-star
RUN Invoke-BashCmd rm -rf FStar/mitls-fstar
RUN Invoke-BashCmd rm -rf FStar/vale

RUN Invoke-BashCmd rm -f FStar/build.sh
RUN Invoke-BashCmd rm -f FStar/build_helper.sh
RUN Invoke-BashCmd rm -f FStar/buildlogfile.txt
RUN Invoke-BashCmd rm -f FStar/log_no_replay.html
RUN Invoke-BashCmd rm -f FStar/log_worst.html
RUN Invoke-BashCmd rm -f FStar/orange_status.txt
RUN Invoke-BashCmd rm -f FStar/result.txt
RUN Invoke-BashCmd rm -f FStar/status.txt
RUN Invoke-BashCmd rm -f FStar/commitinfofilename.json

WORKDIR "FStar/vale"
COPY / .

# Do another cleanup
RUN Invoke-BashCmd rm Dockerfile
RUN Invoke-BashCmd rm build.sh
RUN Invoke-BashCmd rm build_helper.sh
RUN Invoke-BashCmd rm id_rsa
RUN Invoke-BashCmd rm commitinfofilename.json
WORKDIR ".."

COPY build.sh build.sh
COPY build_helper.sh build_helper.sh

RUN Invoke-BashCmd ./build_helper.sh $Env:TARGET $Env:BUILDLOGFILE $Env:MAXTHREADS $Env:BRANCHNAME $Env:FSTARSOURCEVERSION '||' true

# Remove ssh key.
RUN Invoke-BashCmd rm .ssh/id_rsa