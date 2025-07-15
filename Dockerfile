# Use PyTorch base image with CUDA and Python
FROM pytorch/pytorch:2.2.2-cuda11.8-cudnn8-runtime

# Set environment variables for non-interactive installs
ENV DEBIAN_FRONTEND=noninteractive

# Install system dependencies
RUN apt-get update && apt-get install -y \
    curl \
    git \
    build-essential \
    libgmp-dev \
    python3 \
    python3-pip \
    python3-venv \
    sudo \
    vim.tiny \
    && rm -rf /var/lib/apt/lists/*

# Install elan (Lean version manager)
RUN curl -sSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | bash -s -- -y

# Add Lean to PATH
ENV PATH="/root/.elan/bin:${PATH}"

# Install Python ML dependencies
RUN pip install --upgrade pip && \
    pip install \
      torch \
      transformers \
      datasets \
      accelerate \
      scikit-learn

# Set working directory (not masked by RunPod)
WORKDIR /opt/app

# Copy everything except what's in .dockerignore
COPY . /opt/app

# Build Lean project
RUN lake exe cache get && lake build Canonical

# Runtime command: keep container alive
CMD ["bash", "-c", "echo 'Container started successfully'; while true; do echo 'Running...'; sleep 30; done"]
