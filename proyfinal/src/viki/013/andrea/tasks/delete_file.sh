#!/usr/bin/bash

find . -type f -name '*roops.core.objects*' -delete && find . -type f -name '*.dals*' -delete && find . -type f -name '*.djals*' -delete
rm -rf java org roops
