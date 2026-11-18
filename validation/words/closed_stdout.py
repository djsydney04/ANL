"""Exec the real CLI with an unwritable stdout descriptor; stderr remains captured."""
import os
import sys
fd = os.open(sys.argv[1], os.O_RDONLY)
os.dup2(fd, 1)
os.close(fd)
os.execv(sys.argv[2], sys.argv[2:])
