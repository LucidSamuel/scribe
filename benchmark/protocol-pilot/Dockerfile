# The base image's cached Mathlib files may be root-readable only.
ARG BASE_IMAGE=scribe:cleanup-validated
FROM ${BASE_IMAGE}
RUN chmod -R a+rX /opt/lean-project /opt/elan
