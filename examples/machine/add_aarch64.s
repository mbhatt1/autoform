// Assemble with: ./autoform.sh --machine examples/machine/add_aarch64.s Add \
//   --assemble aarch64-unknown-linux-gnu --entry 0 \
//   --register x0=3 --register x1=4 --stop 4 --expect x0=7
.text
.global add
add:
    add x0, x0, x1
    ret
