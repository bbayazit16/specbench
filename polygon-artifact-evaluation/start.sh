docker build -t polygon .
docker run --name polygon -it --rm -v "$(pwd)":/polygon -w /polygon polygon
