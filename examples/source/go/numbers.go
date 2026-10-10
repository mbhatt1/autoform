package numbers
func Add(a int64, b int64) int64 { return a + b }
func Div(a int64, b int64) int64 { return a / b }
func Shift(a uint64, b uint) uint64 { return a << b }
func Right(a int64, b uint) int64 { return a >> b }
func Inc(a int64) int64 { a += 1; return a }
func Bump(a int8) int8 { a++; return a }
func Word(a int, b int) int { return a + b }
func ContextShift(n uint) uint32 { return 1 << n }
func Constant() uint64 { return 9223372036854775807 + 1 }
