# M40001/M40009 example sheets and course notes in Lean.

M40001/M40009 is the "introduction to proof" course in the maths department at Imperial College London. In the 2020 directory I am currently putting the 2020 example sheets.

## How to try the example sheets in Lean

You have two options: (1) use Lean online or (2) install it onto your computer.

### (1) : use Lean online.

Here are the problem sheets for October 2020:

[Sheet 1](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2FM40001_lean%2Fmaster%2Fsrc%2F2020%2Fquestions%2Fsheet1.lean).

(more sheets to come).

Here are the 2019 sheets:

[Sheet 1](https://tinyurl.com/Lean-M40001-Example-Sheet-1).

[Sheet 2](https://tinyurl.com/Lean-M40001-Example-Sheet-2).

[Sheet 3](https://tinyurl.com/Lean-M40001-Example-Sheet-3).

[Sheet 4](https://tinyurl.com/Lean-M40001-Example-Sheet-4).



### (2) Download the project and try the example sheets on your own computer

This only works if you have Lean and mathlib installed. Instructions for installing Lean and mathlib are
[here at the Leanprover community website](https://leanprover-community.github.io/get_started.html#regular-install).

If lean and mathlib are installed, then change to the directory where you keep your Lean projects, and install it by typing this into the command line (perhaps in a directory where you want to keep your Lean projects).

```
$ leanproject get https://github.com/ImperialCollegeLondon/M40001_lean
```

Open the project in VS Code e.g. by selecting `File` -> `Open Folder` and then selecting the `M40001_lean` directory. Then look in the `src/questions` directory for the problem sheets.
