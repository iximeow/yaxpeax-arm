## yaxpeax-arm

### ! user beware !
* armv7 NEON support is still nonexistent

## arch notes:

### Register Names
Reproduced from [infocenter.arm.com](http://infocenter.arm.com/help/index.jsp?topic=/com.arm.doc.dui0473c/CJAJBFHC.html):
| Name | Maps To | Meaning |
| ---- | ------- | ------- |
| r0-r15 | r0-r15 | These are the the registers! |
| a1-a4 | r0-r3 | Argument, result, or scratch registers |
| v1-v8 | r4-r11 | Variable registers |
| sb | r9 | Static base register |
| fp | r11 | Frame pointer\* |
| ip | r12 | Intra-procedure call register |
| sp | r13 | Stack pointer |
| lr | r14 | link register |
| pc | r15 | program counter |

\* `fp` does not appear to be explicitly referenced in ARM documentation, and mapping to r11 looks to be OS (Windows/Linux?) convention.
