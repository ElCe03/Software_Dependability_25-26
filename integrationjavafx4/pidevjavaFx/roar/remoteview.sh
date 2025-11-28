#!/bin/bash

Xvfb :0 -screen 0 1280x800x24 &

sleep 2

fluxbox &

x11vnc -display :0 -forever -nopw -quiet &

websockify --web /usr/share/novnc/ --wrap-mode=ignore --log-file=/tmp/novnc.log 8080 localhost:5900 &

echo "Avvio CliniCare..."
java -Dprism.order=sw -jar app.jar
