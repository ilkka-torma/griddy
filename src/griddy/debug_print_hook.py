import builtins
import inspect

old_print = builtins.print

def traced_print(*args, **kwargs):
    frame = inspect.stack()[1]  # caller info
    old_print(f"[PRINT @ {frame.filename}:{frame.lineno}]", *args, **kwargs)

builtins.print = traced_print
