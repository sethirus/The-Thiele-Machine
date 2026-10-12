from pathlib import Path
R=Path(__file__).parent
p=R/'quantum-constructions.tex';s=p.read_text()
s=s.replace(r'''c_0=\frac{y-x\cos\delta}{\sin\delta},\quad
c_1=\frac{w-z\cos\delta}{\sin\delta},\quad
 a_0=xe_1+c_0e_2+\sqrt{1-x^2-c_0^2}\,e_3,\quad
 a_1=ze_1+c_1e_2+\sqrt{1-z^2-c_1^2}\,e_4.''',r'''\begin{aligned}
c_0&=\frac{y-x\cos\delta}{\sin\delta},&
c_1&=\frac{w-z\cos\delta}{\sin\delta},\\
a_0&=xe_1+c_0e_2+\sqrt{1-x^2-c_0^2}\,e_3,\\
a_1&=ze_1+c_1e_2+\sqrt{1-z^2-c_1^2}\,e_4.
\end{aligned}''')
s=s.replace(r'''P_0(a_0,a_1,b)=\frac{1+t a_0a_1+x a_0b+z a_1b}{8},\qquad
P_1(a_0,a_1,b)=\frac{1+t a_0a_1+y a_0b+w a_1b}{8}.''',r'''\begin{aligned}
P_0(a_0,a_1,b)&=\frac{1+t a_0a_1+x a_0b+z a_1b}{8},\\
P_1(a_0,a_1,b)&=\frac{1+t a_0a_1+y a_0b+w a_1b}{8}.
\end{aligned}''')
p.write_text(s)
p=R/'universal-construction.tex';s=p.read_text().replace('Every\nsubsequent address therefore increases by 3, including all referenced targets.','Every\nblock after the head therefore starts three addresses later. Resolve targets to those\nnew addresses; the head itself remains at address 1.')
p.write_text(s)
p=R/'apply_self_contained.py';s=p.read_text();anchor="s=re.sub(r'\\n{3,}','\\n\\n',s)"
extra='''# Keep historical credit without making the definitions depend on software.
s=s.replace("library and I use Minsky's version and Minsky's name.","machine uses Minsky's version and Minsky's name.")
s=s.replace("counting from 1 the way the library's two-counter machine does", "counting from 1")
s=s.replace("the library's two-counter\\nmachine, which it calls a Minsky machine, numbers its lines from 1", "the two-counter\\nmachine used by Forster, Larchey-Wendling and coauthors numbers its lines from 1")
s=s.replace("with halting reduced to the library's", "with halting reduced from two-counter halting")
s=s.replace("L's recursion theorem, Rice and halting, checked; the library's compiler used to put every computably presented Thiele machine on the universal host", "L's recursion theorem, Rice and halting; a counter compilation putting every computably presented Thiele machine on the universal host")
s=s.replace("There's a decider for it with a soundness proof, in two", "There's a certificate checker for it with a soundness proof, in two")
s=s.replace("is not proved here. It's a decider with a soundness proof, as", "is not proved here. The certificate checker is sound, as")
'''
assert anchor in s;s=s.replace(anchor,extra+'\n'+anchor);p.write_text(s)
