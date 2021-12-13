class Let {
    name: string;
    value: string;
    size: number;
    isExpanded: boolean;
    expandedSize: number;
    externalLets: { [key: string]: { let: Let; idx: number[] } };

    constructor(name: string, letText: string, letsList: { [key: string]: Let }, indices: { [key: number]: string }) {
        this.name = name;
        this.value = letText;
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

        this.size = this.getTextWidth(letText);
        this.expandedSize = this.getTextWidth(this.expandValue());
    }

    expandValue = (): string => {
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
        return letText;
    };

    fitsTheWindow = (windowSize: number): boolean => {
        const size = this.isExpanded ? this.expandedSize : this.size;
        return size <= windowSize;
    };

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
}

export default Let;
