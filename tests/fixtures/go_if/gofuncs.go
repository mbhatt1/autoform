package main

func plain(x int) int {
	if x > 0 {
		return x
	}
	return 0
}

func ifelse(x int) int {
	if x > 0 {
		return 1
	} else {
		return -1
	}
}

func chain(x int) int {
	if x > 10 {
		return 3
	} else if x > 5 {
		return 2
	} else {
		return 1
	}
}

func withInit(x int) int {
	if v := double(x); v > 10 {
		return v
	}
	return 0
}

func initElse(x int) int {
	if v := double(x); v > 10 {
		return v
	} else if v > 4 {
		return v + 1
	}
	return 0
}

func nested(x int) int {
	if x > 0 {
		if x > 5 {
			return 2
		}
		return 1
	}
	return 0
}

// Two inits of the same name in sequence: each is assigned before it is read.
func twoInits(x int) int {
	r := 0
	if v := x + 1; v > 3 {
		r = r + v
	}
	if v := x * 2; v > 3 {
		r = r + v
	}
	return r
}

// An init variable that shadows a binding visible at the `if` stays the named hole
// `stmt:go-if-init`: an outer local, a parameter, a package variable, an enclosing
// `if`'s init, or a later declaration of the same name.
var g = 7

func shadowLocal(x int) int {
	v := 1
	if v := x; v > 0 {
		v = v + 10
	}
	return v
}

func shadowParam(x int) int {
	if x := x + 1; x > 3 {
		return x
	}
	return x
}

func shadowGlobal(x int) int {
	if g := x; g > 0 {
		g = g + 1
	}
	return g
}

func shadowInit(x int) int {
	if v := x + 1; v > 0 {
		if v := v * 10; v > 20 {
			return v
		}
		return v
	}
	return 0
}

func laterVar(x int) int {
	r := 0
	if v := x + 1; v > 3 {
		r = r + v
	}
	var v int
	return r + v
}

func double(x int) int {
	return x * 2
}
