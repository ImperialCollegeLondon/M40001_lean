# M40001/M40009 example sheets and course notes in Lean.

M40001/M40009 is the "introduction to proof" course in the maths department at Imperial College London. I (Kevin Buzzard) am formalising the part of the course that I am running.

Over time expect course notes and example sheets to appear.

Current state: no course notes, but all four example sheets.

# How to try the example sheets in Lean

## Try the example sheets online

[NB the questions are in the pdf directory of this repository]

[Sheet 1](https://tinyurl.com/Lean-M40001-Example-Sheet-1).

[Sheet 2](https://tinyurl.com/Lean-M40001-Example-Sheet-2).

[Sheet 3](https://tinyurl.com/Lean-M40001-Example-Sheet-3).

[Sheet 4](https://tinyurl.com/Lean-M40001-Example-Sheet-4).



## Download the project and try the example sheets on your own computer

This only works if you have Lean and mathlib installed. Instructions for installing Lean and mathlib are [here at the mathlib github repository](https://github.com/leanprover-community/mathlib#installation).

If lean and mathlib are installed, then change to the directory where you keep your Lean projects, and install it by typing this:

```
$ leanproject get https://github.com/ImperialCollegeLondon/M40001_lean.git
```

Open the project in VS Code e.g. by selecting `File` -> `Open Folder` and then selecting the `M40001_lean` directory. Then look in the `src/questions` directory for the problem sheets.
