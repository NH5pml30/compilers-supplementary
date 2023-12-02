# this is equivalent C-signature for this function
# size_t call_function_with_stack(void *stack, void *func_ptr)

    .globl call_function_with_stack
    .type call_function_with_stack, @function
call_function_with_stack:
    pushl %ebp
    pushl %edi
    movl %esp, %ebp

    # store old stack pointer
    movl %esp, %edi

    # move esp to point to the virtual stack
    movl 12(%ebp), %esp

    # call the function
    movl 16(%ebp), %eax
    call *%eax

    # restore the old stack pointer
    movl %edi, %esp

    # pop the old frame pointer and return
    popl %edi
    popl %ebp            # epilogue
    ret
