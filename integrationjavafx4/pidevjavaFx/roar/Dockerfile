FROM eclipse-temurin:17-jre

WORKDIR /app
ENV DISPLAY=:0
ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
    xvfb \
    fluxbox \
    x11vnc \
    novnc \
    python3-websockify \
    python3-numpy \
    libx11-6 \
    libxext6 \
    libxrender1 \
    libxtst6 \
    libxi6 \
    libgtk-3-0 \
    libgl1 \
    && rm -rf /var/lib/apt/lists/*


RUN ln -s /usr/share/novnc/vnc.html /usr/share/novnc/index.html

COPY CliniCare.jar app.jar
COPY remoteview.sh remoteview.sh

RUN chmod +x remoteview.sh

EXPOSE 8080

ENTRYPOINT ["./remoteview.sh"]




