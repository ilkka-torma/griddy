#!/bin/sh

TILER=1
while getopts ":t:h" opt ; do
    case $opt in
	t)
	    TILER=0
	    ;;
	\?)
	    echo "Invalid option: -$OPTARG (use -t to exclude tiler-specific packages)" >&2
	    exit
	    ;;
    esac
done

# The Lark module is used to parse Diddy code.
pip install lark

# The python-sat module (imported as pysat) is used to solve SAT instances.
# Do NOT install the module called pysat!
pip install python-sat

# The frozendict module provides an immutable dictionary.
pip install frozendict

# The pulp module solves linear programs.
pip install pulp

# The psutil module allows querying memory usage and such.
pip install psutil

# Use the -t option if you don't want to install the following tiler-specific packages.
if [ $TILER -eq 1 ]; then
    # The pygame module is used when running tiler.
    pip install pygame
    
    # The pygame_gui module adds some ui components to pygame.
    pip install pygame_gui
    
    # The numpy module is currently only used to invert a matrix in tiler.
    pip install numpy
fi
