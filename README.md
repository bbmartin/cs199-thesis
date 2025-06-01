# Python to COQ Translator with Automatic Theorem Generation (v1.0.0)

A program that is able to take Python code from a file and output usable COQ code with theorems that verify the translated code

## Dependencies

* Lark (Version: 1.2.2)

## Getting Started

Make sure first that the libraries listed in `requirements.txt` have been installed.

```
pip install -r requirements.txt
```

The first argument of the command shown below should be the filepath that leads to the Python code to be translated. The second argument is where the output file containing the translated Coq file is located (and will be created if it doesn't exist).

```
python -m src.main input_file.py output_file.txt
```

## How to Define Code Blocks

The translator sees code blocks as isolated snippets of code that performs a single task and has no connection to any other code blocks within the same input file. Each well-defined code block is then translated into Coq. These are usually prefaced with **flags**, Python comments that start with a very specific set of characters so that the parser treats them differently from ordinary comments. 

The following flags are used in both separating code blocks from one another, as well as providing context for the translation:

### `#s:` flag

This is a required flag used in signifiying the start of a code block, as well as providing the primary data type being manipulated within the code block. The form is as follows:
```python
#s: <data_type>
```
Example:
```python
#s: int
# This will be seen as a regular Python comment.
x = 0
for i in range(10):
    ...
```

### `#v:` flag

This flag is not required but highly recommended to use as this highlights any variables used in the code block and will be stored for later use when translating the Python code into Coq. It takes the following form:
```python
#v: [...list_of_variable_names]
```
Example:
```python
#s: int
#v: [x, lst]
x = 0
lst = [1, 2, 3, 4, 5]
for i in lst:
    ...
```

**Note**: To see more examples, refer to `intput.py`, with `output.txt` containing the direct translations.

## Supported Test Cases

The following test cases are Python code blocks that the translator currently supports (which can be seen in `input.py` for reference):

### `if-else` statement
1. Comparing and assigning strings

    Sample Python Code:
    ```python
    #s: str
    #v: [x]
    x = "yellow"
    if x == "green":
        x = "yellow"
    elif x == "yellow":
        x = "red"
    else:
        x = "green"
    ```

    Coq Direct Translation:
    ```coq
    Definition if_struct_0 (x : string) : string :=
        if string_dec x "green"%string then
            "yellow"%string
        else if string_dec x "yellow"%string then
            "red"%string
        else
            "green"%string.
    ```

2. Basic arithmetic based on numerical comparisons
    
    Sample Python Code:
    ```python
    #s: int
    #v: [x]
    x = 10
    if x > 1:
        x = x + 1
    elif x < -1:
        x = x - 1
    else:
        x = 0
    ```

    Coq Direct Translation:
    ```coq
    Definition if_struct_1 (x : Z) : Z :=
        if Z.gtb x (1) then
            x + 1
        else if Z.ltb x (-1) then
            x - 1
        else
            0.
    ```

### `for` loop 
1. Adding numbers in a range
   
    Sample Python Code:
    ```python
    #s: int
    #v: [y]
    y = 0
    for i in range(10):
        y = y + i
    ```

    Coq Direct Translation:
    ```coq
    Definition for_loop_2 {A : Type}
        (start end_ : nat)
        (body : nat -> A -> A)
        (init : A) : A :=
        let fix helper remaining current init :=
            match remaining with
            | O => init
            | S rem =>
                if current <? end_ then
                    helper rem (current + 1) (body current init)
                else
                    init
            end
        in helper (end_ - start) start init.

    Definition for_loop_operation_2 (n : nat) : nat :=
        for_loop_2 0 10 (fun i y => y + i) n.
    ```

2. Adding numbers in a list

    Sample Python Code:
    ```python
    #s: int
    #v: [y, items]
    y = 0
    items = [1, 2, 3, 4, 5]
    for i in items:
        y = y + i
    ```

    Coq Direct Translation:
    ```coq
    Fixpoint for_loop_list_3 {A B : Type}
        (op : A -> B -> B)
        (init : B)
        (lst : list A)
    : B :=
        match lst with
        | [] => init
        | x :: xs => for_loop_list_3 op (op x init) xs
        end.

    Definition for_loop_list_operation_3 (nums : list nat) : nat :=
        for_loop_list_3 (fun x acc => acc + x) 0 nums.
    ```

3. Concatenating strings in a list

    Sample Python Code:
    ```python
    #s: str
    #v: [y, items]
    y = ""
    items = ["a", "b", "c", "d", "e"]
    for i in items:
        y = y + i
    ```

    Coq Direct Translation:
    ```coq
    Definition for_loop_4 {A : Type}
        (start end_ : nat)
        (body : nat -> A -> A)
        (init : A) : A :=
        let fix helper remaining current init :=
            match remaining with
            | O => init
            | S rem =>
                if current <? end_ then
                    helper rem (current + 1) (body current init)
                else
                    init
            end
        in helper (end_ - start) start init.

    Definition list_strings : list string := ["a"%string; "b"%string; "c"%string; "d"%string; "e"%string].
    Definition for_loop_operation_4 : string :=
        @for_loop_4 string 0 (List.length list_strings)
            (fun (i : nat) (acc : string) =>
                String.append acc (nth i list_strings ""%string))
            ""%string.
    ```

### `while` loop
1. Repeated arithmetic operations

    Sample Python Code:
    ```python
    #s: int
    #v: [z]
    z = 0
    while z < 10:
        z = z + 1
    ```

    Coq Direct Translation:
    ```coq
    Fixpoint while_loop_5 (z : nat) (fuel : nat) {struct fuel} : nat :=
        match fuel with
        | O => z
        | S fuel' =>
            if z <? 10 then
                while_loop_5 (z + 1) fuel'
            else z
        end.
    ```

2. Repeated string concatenation
   
   Sample Python Code:
   ```python
    #s: str
    #v: [z, count]
    z = ""
    count = 0
    while count < 10:
        z = z + "a"
        count = count + 1
    ```

    Coq Direct Translation:
    ```coq
    Fixpoint while_loop_str_6 (z : string) (count : nat) (fuel : nat) {struct fuel} : string :=
        match fuel with
        | O => z
        | S fuel' =>
            if count <? 10 then
                while_loop_str_6 (z ++ "a"%string) (count + 1) fuel'
            else
                z
        end.
    ```

## Theorems

