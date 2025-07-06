FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
    curl \
    git \
    python3 \
    poppler-utils \
    texlive-luatex \
    texlive-latex-extra \
    texlive-pictures \
    texlive-fonts-extra \
    texlive-fonts-recommended \
    fonts-inter \
    fonts-texgyre \
    fonts-font-awesome \
    gcc \
    build-essential \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y

ENV PATH="/root/.elan/bin:${PATH}"

WORKDIR /app
COPY . .

RUN lake exe generate-manual --depth 2

EXPOSE 8880

CMD ["python3", "server.py", "8880"]
