

The task is to create a simple key value store with a slightly different query option. Neither the key nor the value has any restriction on size, type of data (if the user want they could use a picture as a key or any other binary formatted data). Despite of the lack of restriction on the data format, as a convienance the user should have at least two interface for inserting data into the storage, the first restricts text based data, the second option is the full mode without any restriction.

The basic operation must be supported: creating, removing, modifying the key value entries.

Note: in the examples the simplified api is used with textual representation; and the raw data version should follow the sameish notation.
```
$ create key=value
key created.
$ remove key
key removed.
$ remove key.
key does not exitst.
$ set key=value
key created.
$ set key=value1
key updated.
```

The main difference is how the data can be requested from the database. The user must query a key, but the database does not look up the key and if exists returns with it content. Rather it uses the key as a starting point of a sentence and returns a response value that is a plausable response based on the current values. Further elaboration on what is a plausable response.

The user provided keys and values now should be dealt with as one sentence concatenating the key with value[1]. Those sentences can be divided into words via a configurable word definition (user could define a word definition with a regular expression[2]). Based on those sentences a possible sequence of words are defined, and each word has a possible follow up sentence A word has p probablitiy of follow up sentence B if p equals to a number of occurance of A B divided by a number of occurance of A C where length(B) = length(C). The length used by a program is user provided value that is global and not local to the query. The length(X) function here is defined as the number of words in X. Generating an infinite amount of text is possible if for a word A always choose a sentence B, if there is multiple possible B choose one randomly based on its probablity, if there is no such B use the pool of the stored keys with equal probablity.

The plausable response to a key A should be a subsentence of an infinite sentece generated via the above method, where the length of the subsentence could be configurable with the number of words. That is a global option for the program, that may be changed durring execution.

The words not matching the current word definition should be skipped, but the user should be warned that there is a word(s) skipped by their rule.

Example:
```
$ word_rule=[^ ]+
$ sentence_length=1
$ insert dog=food
$ query cat
cat dog
$ insert cat=fish
$ query cat
cat fish
$ insert dog=cat are not dog's friends
$ query dog
dog food
$ query dog
dog friends
```



[1] Note: the key could be a non-word by itself

[2] Note: the end of data is always a word end by definition
