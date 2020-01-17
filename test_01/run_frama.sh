#!/bin/bash

#Make sure the list of provers is up to date
why3 config --detect

#Run the gui
frama-c-gui -wp -rte -kernel-msg-key pp main.c
