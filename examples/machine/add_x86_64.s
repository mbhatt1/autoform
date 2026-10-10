# Assemble with: ./autoform.sh --machine examples/machine/add_x86_64.s Add \
#   --assemble x86_64-unknown-linux-gnu --entry 0 \
#   --register RDI=3 --register RSI=4 --stop 4 --expect RAX=7
.text
.global add
add:
    lea (%rdi,%rsi), %rax
    ret
