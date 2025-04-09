main:
  endbr64
  movabs $0x7fffffff80000000,%rcx
  movabs $0x800000007fffffff,%r13
  movabs $0x7fffffff7fffffff,%r15
target:
  cmp    %r10,%r8
  mov    %r8,%rax
  mov    %r10,%rbx
  mov    %rcx,%rbp
  mov    %r13,%r14
  cmovb  %r10,%r8
  cmovb  %rax,%r10
  cmovb  %r13,%rcx
  cmovb  %rbp,%r13
  sub    %r10,%r8
  sub    %r13,%rcx
  add    %r15,%rcx
  test   $0x1,%rax
  cmove  %rax,%r8
  cmove  %rbx,%r10
  cmove  %rbp,%rcx
  cmove  %r14,%r13
  shr    %r8
  add    %r13,%r13
  sub    %r15,%r13
  sub    $0x1,%edi
  jne target
  shr    $0x20,%r15
  mov    %ecx,%edx
  mov    %r13d,%r12d
  shr    $0x20,%rcx
  shr    $0x20,%r13
  sub    %r15,%rdx
  sub    %r15,%rcx
  sub    %r15,%r12
  sub    %r15,%r13
  repz retq
