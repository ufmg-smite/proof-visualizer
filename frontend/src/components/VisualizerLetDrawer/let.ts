interface Line {
    value: string;
    indentLevel: number;
}

class Let {
    name: string;
    value: string;
    lines: Line[];
    biggerID: number;
    isExpanded: boolean;
    externalLets: { [key: string]: { let: Let; idx: number[] } };

    constructor(name: string, letText: string, letsList: { [key: string]: Let }, indices: { [key: number]: string }) {
        this.name = name;
        this.value = letText;
        this.lines = [{ value: letText, indentLevel: 0 }];
        this.biggerID = 0;
        this.isExpanded = false;

        this.externalLets = {};
        Object.keys(indices).forEach((key) => {
            const numKey = Number(key);
            const letName = indices[numKey];
            this.externalLets[letName] = {
                let: letsList[letName],
                idx: this.externalLets[letName] ? [...this.externalLets[letName].idx, numKey] : [numKey],
            };
        });
    }

    getTextWidth = (text: string): number => {
        const canvas = document.createElement('canvas');
        const context = canvas.getContext('2d');
        let size = 0;
        if (context) {
            context.font =
                '14px / 18px -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Oxygen, Ubuntu, Cantarell, "Open Sans", "Helvetica Neue", Icons16, sans-serif';
            size = context.measureText(text).width;
        }
        return size;
    };

    expandValue = (shouldUpdate = false): string => {
        const keyList = Object.keys(this.externalLets).map((key) => this.externalLets[key].let.name);
        let letText = this.value;

        // Iterate from the last to the first external let
        for (let i = keyList.length - 1; i >= 0; i--) {
            const letName = keyList[i];

            // For each let, iterate through all the indexes they show up inside the string
            for (let k = this.externalLets[letName].idx.length - 1; k >= 0; k--) {
                const idx = this.externalLets[letName].idx[k];

                // Expand all the terms
                letText =
                    letText.substring(0, idx) +
                    this.externalLets[letName].let.expandValue() +
                    letText.substring(idx + letName.length, letText.length);
            }
        }
        if (shouldUpdate) {
            this.lines = [{ value: letText, indentLevel: 0 }];
            this.biggerID = 0;
        }
        return letText;
    };

    expandPartialy = (externalRef: Let, letIdx: number): string => {
        const key = externalRef.name;
        const indentedText = this.printLines();

        let lastLine = 0,
            count = 0,
            i;
        // Iterates through the first lines until the point we reach the changed line
        for (i = 0; i < this.lines.length; i++) {
            lastLine = this.lines[i].value.length + 4 * this.lines[i].indentLevel + 1;
            count += lastLine;
            if (letIdx < count) break;
        }
        // New index (points to the start of the line content (ignores initial indent white space))
        const newIdx = letIdx - (count - lastLine + 4 * this.lines[i].indentLevel);

        // Update the new line to the new content
        this.lines[i].value =
            this.lines[i].value.substring(0, newIdx) +
            externalRef.value +
            this.lines[i].value.substring(newIdx + key.length, this.lines[i].value.length);

        // Returns the indented text with the content to be replaced
        return (
            indentedText.substring(0, letIdx) +
            externalRef.value +
            indentedText.substring(letIdx + key.length, indentedText.length)
        );
    };

    shrinkValue = (): string => {
        this.lines = [{ value: this.value, indentLevel: 0 }];
        this.biggerID = 0;
        return this.value;
    };

    fitsTheWindow = (windowSize: number): boolean => {
        const line = this.lines[this.biggerID];
        const size = this.getTextWidth(`${'    '.repeat(line.indentLevel)}${line.value}`);
        return size < windowSize;
    };

    indent = (windowSize: number, mode: boolean): string => {
        let someDoesntFit;
        if (mode) someDoesntFit = true;
        else someDoesntFit = this.getTextWidth(this.lines[this.biggerID].value) < windowSize ? false : true;

        // While there are lines that doesn't fit the window size
        while (someDoesntFit) {
            const { lines, biggerID } = this;
            const newLines: Line[] = [];
            const thisLevel = lines[biggerID].indentLevel;
            const thisLine = lines[biggerID].value;

            let lastSpace = -1,
                lastUsedSpace = -1,
                lastOpenParenthesis = -1,
                indent = lines[biggerID].indentLevel - 1,
                biggestSize = 0,
                newBiggerID = 0;

            // Iterate through the line and calculate the indentation levels
            for (let i = 0; i < thisLine.length; i++) {
                const c = thisLine[i];
                // Opening parenthesis
                if (c === '(') {
                    indent++;
                    // If it's one of the arguments of the operation
                    if (indent === thisLevel + 1) lastOpenParenthesis = i;
                }
                // Closing parenthesis
                else if (c === ')') {
                    // If it's the end of this line
                    if (indent === thisLevel) {
                        // If the last argument was not inserted
                        if (thisLine[i - 1] !== ')') {
                            newLines.push({
                                value: thisLine.substring(lastSpace + 1, i),
                                indentLevel: indent + 1,
                            });
                        }
                        newLines.push({ value: ')', indentLevel: indent });
                    }
                    // If it's the end of this argument
                    else if (indent === thisLevel + 1) {
                        newLines.push({
                            value: thisLine.substring(lastOpenParenthesis, i + 1),
                            indentLevel: indent,
                        });
                    }
                    indent--;
                }
                // If a new space is detected in the current identation level
                //   and the last argument is not between parenthesis
                else if (c === ' ') {
                    lastSpace = i;

                    if (indent === thisLevel) {
                        if (thisLine[i - 1] !== ')') {
                            newLines.push({
                                value: thisLine.substring(lastUsedSpace + 1, i),
                                indentLevel: newLines.length ? indent + 1 : indent,
                            });
                        }
                        lastUsedSpace = i;
                    }
                }
            }

            // Insert new lines if happend some indentation
            if (newLines.length > 0) this.lines.splice(biggerID, 1, ...newLines);

            // Find the new biggest line
            this.lines.forEach((line, id) => {
                // Get the size of this new line
                const thisSize = this.getTextWidth(`${'    '.repeat(line.indentLevel)}${line.value}`);
                if (thisSize > biggestSize) {
                    biggestSize = thisSize;
                    newBiggerID = id;
                }
            });

            this.biggerID = newBiggerID;

            // If the biggest size fits the window or no new line was found (minimal indentation)
            if (biggestSize < windowSize || newLines.length < 1) someDoesntFit = false;
        }
        return this.printLines();
    };

    groupUp = (): string => {
        let original = '';
        // Group up all the lines into one single string
        this.lines.forEach((line, id, self) => {
            original += line.value;
            if (id < self.length - 1 && self[id + 1].value !== ')') {
                original += ' ';
            }
        });
        return original;
    };

    printLines = (): string => {
        return this.lines.reduce((ac, line) => (ac += `${'    '.repeat(line.indentLevel)}${line.value}\n`), '');
    };
}

export default Let;
