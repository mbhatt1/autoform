"""Private scalar C ABI worker. Invoked with Python -I by native_c.py."""
import ctypes
import json
import os
import resource
import sys


TYPES = {tag: getattr(ctypes, 'c_' + ('int' if tag[0] == 'i' else 'uint') + tag[1:])
         for tag in ('i8', 'u8', 'i16', 'u16', 'i32', 'u32', 'i64', 'u64')}


def execute(request):
    # Loading the library can execute constructors. It must happen only here,
    # after the parent has established a process group and deadline.
    library = ctypes.CDLL(request['library'])
    if request['operation'] == 'probe':
        for symbol in request['symbols']:
            getattr(library, symbol)
        return dict(status='ok')
    if request['operation'] != 'call' or request['repeat'] not in (1, 2):
        raise ValueError('invalid native worker request')
    fn = getattr(library, request['symbol'])
    fn.argtypes = [TYPES[t] for t in request['arguments']]
    fn.restype = TYPES[request['result']]
    return dict(status='ok', values=[fn(*request['values']) for _ in range(request['repeat'])])


def main():
    fd = int(sys.argv[1])
    os.set_inheritable(fd, False)
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    try:
        response = execute(json.load(sys.stdin))
    except Exception as exc:
        response = dict(status='error', detail=(type(exc).__name__ + ': ' + str(exc))[:2000])
    # A separate descriptor keeps native stdout/stderr out of the result protocol.
    # The parent still requires clean process exit; an abrupt destructor cannot
    # leave a successful observation behind merely by failing after this write.
    with os.fdopen(fd, 'w') as output:
        json.dump(response, output)


if __name__ == '__main__':
    main()
