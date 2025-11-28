
FROM eclipse-temurin:17-jre

WORKDIR /app
RUN apt-get update && apt-get install -y --no-install-recommends \
    libx11-6 \
    libxext6 \
    libxrender1 \
    libxtst6 \
    libxi6 \
    libgtk-3-0 \
    libgl1 \
    && rm -rf /var/lib/apt/lists/*

COPY CliniCare.jar app.jar

EXPOSE 8080

ENTRYPOINT ["java", "-jar", "app.jar"]




