function shift(a, b) { return a << b; }
function unsigned(a, b) { return a >>> b; }
function signed(a, b) { return a >> b; }
function bits(a, b) { return a | b; }
function complement(a) { return ~a; }
function signedAssign(a, b) { a >>= b; return a; }
function unsignedAssign(a, b) { a >>>= b; return a; }
function unsignedValue(a, b) { return a >>>= b; }
function add(a, b) { return a + b; }
