import React, { useEffect, useRef, useState } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { connect } from 'react-redux';
import { useAppSelector, useAppDispatch } from '../../store/hooks';
import { selectDot, selectFileName, set } from '../../store/features/file/fileSlice';
import {
    applyView,
    changeStyle,
    selectNodes,
    applyColor,
    hideNodes,
    foldAllDescendants,
    unfoldNodes,
    selectVisualInfo,
    selectProof,
    selectHiddenNodes,
    selectView,
    unselectNodes,
    process,
    setSmt,
} from '../../store/features/proof/proofSlice';
import { ReduxState, NavbarPropsAndRedux, NavbarProps } from '../../interfaces/interfaces';

import { Alignment, Button, Icon, InputGroup, Navbar, Switch, Menu, MenuItem } from '@blueprintjs/core';
import { Popover2 } from '@blueprintjs/popover2';
import { selectTheme, toggle } from '../../store/features/theme/themeSlice';
import '../../scss/VisualizerNavbar.scss';
import { allowRenderNewFile, findNode, reRender } from '../../store/features/externalCmd/externalCmd';
import examples from '../../examples/proofs-examples';
import { ConvertToSVG } from './SVGConverter';

function useWindowSize() {
    // Initialize state with undefined width/height so server and client renders match
    // Learn more here: https://joshwcomeau.com/react/the-perils-of-rehydration/
    const [windowSize, setWindowSize] = useState({
        width: 0,
        height: 0,
    });
    useEffect(() => {
        // Handler to call on window resize
        function handleResize() {
            // Set window width/height to state
            setWindowSize({
                width: window.innerWidth,
                height: window.innerHeight,
            });
        }
        // Add event listener
        window.addEventListener('resize', handleResize);
        // Call handler right away so state gets updated with initial window size
        handleResize();
        // Remove event listener on cleanup
        return () => window.removeEventListener('resize', handleResize);
    }, []); // Empty array ensures that effect is only run on mount
    return windowSize;
}

function isNotMozzila() {
    const userAgent = navigator.userAgent;
    let browserName;

    if (userAgent.match(/chrome|chromium|crios/i)) {
        return true;
    } else if (userAgent.match(/firefox|fxios/i)) {
        return false;
    } else if (userAgent.match(/safari/i)) {
        return true;
    } else if (userAgent.match(/opr\//i)) {
        return true;
    } else if (userAgent.match(/edg/i)) {
        return true;
    }
    return browserName;
}
const isNotMozz = isNotMozzila();

const colorMap: { [name: string]: string } = {
    red: '#f72b34',
    orange: '#ff8334',
    yellow: '#ffc149',
    green: '#60aa51',
    blue: '#0097e4',
    purple: '#a73da5',
    brown: '#a95a49',
    gray: '#464646',
    white: '#f0f0f0',
};

const VisualizerNavbar: React.FC<NavbarPropsAndRedux> = ({
    setDialogIsOpen,
    setDrawerIsOpen,
    addErrorToast,
    setInTutorial,
    setSmtDrawerIsOpen,
    inTutorial,
    visualInfo,
    proof,
    dot,
    view,
    hiddenNodes,
    hideNodes,
}: NavbarPropsAndRedux) => {
    const fileName = useAppSelector(selectFileName);
    const darkTheme = useAppSelector(selectTheme);
    const windowSize = useWindowSize();
    const [command, setCommand] = useState('');
    const [lastCommands, setLastCommands] = useState(['']);
    const [commandId, setCommandId] = useState(0);
    const [matchableCmd, setMatchableCmd] = useState<string[]>([]);
    const [matchableCmdIsOpen, setMatchableCmdIsOpen] = useState(false);

    const dispatch = useAppDispatch();

    const commandsMap: { [cmd: string]: (cmds: string[]) => void } = {
        ['/view']: (cmds: string[]) => {
            switch (cmds[1]) {
                case 'full':
                    dispatch(applyView('full'));
                    dispatch(reRender());
                    break;
                case 'clustered':
                    dispatch(applyView('clustered'));
                    dispatch(reRender());
                    break;
                case 'colored-full':
                    dispatch(applyView('colored-full'));
                    dispatch(reRender());
                    break;
            }
        },
        ['/select']: (cmds: string[]) => {
            if (cmds[1]) {
                let cmdArg = '';
                cmds.forEach((string, id) => id !== 0 && (cmdArg += string + ' '));
                // Matches all the brackets
                const matches = [...cmdArg.matchAll(/\[([^\[\]]+)\]/g)];
                let idList: number[] = [];

                // There is a case with brackets
                if (matches[0]) {
                    const insideBracket = matches[0][1].trim();
                    let insideMatches = [...insideBracket.matchAll(/\s*\d+\s*-\s*\d+\s*/g)];

                    // Number range notation
                    if (insideMatches[0]) {
                        // Get the range limits
                        const rangeLim = insideMatches[0][0].split(/\s*-\s*/).map((numS) => Number(numS));
                        idList = Array.from({ length: rangeLim[1] - rangeLim[0] + 1 }, (_, i) => rangeLim[0] + i);
                    }
                    // List notation
                    else {
                        insideMatches = [...insideBracket.matchAll(/(\s*\d+\s*,*)+/g)];
                        // Number list notation
                        if (insideMatches[0]) {
                            // Group all the matches
                            let listStr = '';
                            insideMatches.forEach((match) => (listStr += match[0]));
                            // Convert to number
                            idList = listStr
                                .split(/,\s*/)
                                .filter((word) => word.length > 0 && !isNaN(Number(word)))
                                .map((id) => Number(id));
                        }
                    }
                } else {
                    // Is a regex select?
                    const matches = [...cmdArg.matchAll(/\/[^\/]*\//g)];
                    const argMatch = [...cmdArg.matchAll(/--(c|r)/g)];
                    // If there is a regex
                    if (matches[0]) {
                        let argIsConclusion = true;
                        // Try to find the option
                        if (argMatch[0]) {
                            switch (argMatch[0][1]) {
                                case 'r':
                                    argIsConclusion = false;
                                    break;
                                case 'c':
                                    argIsConclusion = true;
                                    break;
                            }
                        }

                        const regexString = matches[0][0].substring(1, matches[0][0].length - 1);
                        try {
                            // Search all the nodes with the specific regex matching in the conclusion
                            const regex = new RegExp(regexString);
                            idList = proof
                                .filter((node) => regex.test(argIsConclusion ? node.conclusion : node.rule))
                                .map((node) => node.id);
                        } catch (err) {
                            // If the inserted regex expression is invalid (probably missing \)
                            addErrorToast('Regex error: probably and wrong regex expression');
                        }
                    }
                }

                dispatch(selectNodes(idList));
            }
        },
        ['/unselect']: (cmds: string[]) => {
            const allNodesIds = proof.map((node) => node.id);
            dispatch(unselectNodes({ nodes: allNodesIds, cleanAll: true }));
        },
        ['/color']: (cmds: string[]) => {
            if (cmds[1]) {
                // Hex color
                if (RegExp(/^#([0-9a-f]{3}){1,2}$/i).test(cmds[1])) {
                    dispatch(applyColor(cmds[1]));
                    return;
                }
                // Default colors
                if (colorMap[cmds[1]]) dispatch(applyColor(colorMap[cmds[1]]));
            }
        },
        ['/hide']: (cmds: string[]) => {
            // Hide all the selected nodes
            // Re-render the canvas and update the store
            dispatch(reRender());
            dispatch(hideNodes());
        },
        ['/fold']: (cmds: string[]) => {
            // If the option is a number
            if (cmds[1] && !isNaN(Number(cmds[1]))) {
                const nodeId = Number(cmds[1]);
                // Is a valid node
                if (proof.findIndex((node) => node.id === nodeId) !== -1) {
                    // Re-render the canvas and update the store
                    dispatch(reRender());
                    dispatch(foldAllDescendants(nodeId));
                }
            }
        },
        ['/unfold']: (cmds: string[]) => {
            // If there is a number argument
            if (cmds[1] && !isNaN(Number(cmds[1]))) {
                const id = Number(cmds[1]);
                // Get the pi node (to be unfold)
                const obj = proof.find((node) => node.id === id);
                // If it's a pi node
                if (obj && obj.hiddenNodes?.length) {
                    // Re-render the canvas and update the store
                    dispatch(reRender());
                    dispatch(unfoldNodes(id));
                }
            }
        },
        ['/find']: (cmds: string[]) => {
            // If there is an argument and is a number
            if (cmds[1] && !isNaN(Number(cmds[1]))) {
                // Find the node
                dispatch(
                    findNode({
                        nodeId: Number(cmds[1]),
                        option: cmds[2] === '--s',
                    }),
                );
            }
        },
    };
    const commands = useRef(Object.keys(commandsMap)).current;

    const openDialog = (content: string): void => {
        setDialogIsOpen(true);
    };

    const findMatchableCmd = (e: React.ChangeEvent<HTMLInputElement>) => {
        if (e.target.value.length) {
            setMatchableCmd(commands.filter((cmd) => cmd.indexOf(e.target.value) !== -1));
            setMatchableCmdIsOpen(true);
        }
        // If it's an empty string
        else {
            setMatchableCmd([]);
            setMatchableCmdIsOpen(false);
        }
    };

    const renderMatchableCmd = () => {
        if (matchableCmd.length) {
            const list: JSX.Element[] = [];
            matchableCmd.forEach((cmd) => list.push(<MenuItem text={cmd} />));
            return <Menu className="matchable-menu">{list}</Menu>;
        }
        return <></>;
    };

    const handleInputKeyDown = (e: React.KeyboardEvent<HTMLElement>) => {
        // Creates an commands historic, registering the past 4 commands
        switch (e.key) {
            case 'Enter':
                // If the command is not a white space
                if (command.trim() !== '') {
                    runCommands(command);
                    if (lastCommands.length === 5) {
                        lastCommands.pop();
                    }
                    lastCommands.unshift('');
                    setLastCommands(lastCommands);
                    setCommand('');
                }
                setMatchableCmd([]);
                break;
            case 'ArrowUp':
                if (commandId < lastCommands.length - 1) {
                    const newId = commandId + 1;
                    setCommandId(newId);
                    setCommand(lastCommands[newId]);
                    setMatchableCmd([]);
                    setMatchableCmdIsOpen(false);
                }
                break;
            case 'ArrowDown':
                if (commandId > 0) {
                    const newId = commandId - 1;
                    setCommandId(newId);
                    setCommand(lastCommands[newId]);
                    setMatchableCmd([]);
                    setMatchableCmdIsOpen(false);
                }
                break;
        }
    };

    const runCommands = (command: string): void => {
        const cmds = command.trim().split(/ +/);
        // If the command exist
        if (cmds[0] && commandsMap[cmds[0]]) {
            commandsMap[cmds[0]](cmds);
        }
    };

    const exportJSON = () => {
        const downloadJSON = {
            dot: dot,
            visualInfo: visualInfo,
            hiddenNodes: hiddenNodes,
            view: view,
        };
        const fName = fileName.split('.')[0].replace(/\s+/g, '_');

        const link = document.createElement('a');
        link.download = fName + '.json';
        link.href = `data:attachment/text,${encodeURIComponent(JSON.stringify(downloadJSON))}`;
        link.click();
    };

    const exportPNG = (e: React.MouseEvent<HTMLElement, MouseEvent> | null) => {
        e?.preventDefault();
        const link = document.createElement('a');
        link.download = fileName ? `${fileName.split('.')[0].replace(/\s+/g, '_')}.png` : '';
        const graph = document.getElementsByClassName('konvajs-content');
        if (graph.length) {
            link.href = (graph[0].children[0] as HTMLCanvasElement).toDataURL('image/png');
            link.click();
        }
    };

    const exportSVG = (e: React.MouseEvent<HTMLElement, MouseEvent> | null) => {
        e?.preventDefault();

        const el = ConvertToSVG(proof, visualInfo);
        const svg = renderToStaticMarkup(el);

        // Download the svg content
        const base64doc = btoa(unescape(encodeURIComponent(svg)));
        const a = document.createElement('a');
        a.download = fileName ? `${fileName.split('.')[0].replace(/\s+/g, '_')}.svg` : 'download.svg';
        a.href = 'data:image/svg+xml;base64,' + base64doc;
        a.click();
    };

    const runExample = (e: React.MouseEvent<HTMLElement, MouseEvent> | null, ex: string, id: number) => {
        e?.preventDefault();
        const dot = examples[ex].dot;
        const smt = examples[ex].smt;

        dispatch(set({ name: `ex-${id + 1}.dot`, value: dot }));
        dispatch(allowRenderNewFile());
        dispatch(reRender());
        dispatch(setSmt(smt));

        dispatch(process({ proof: dot, fileExtension: 'dot' }));
        setSmtDrawerIsOpen(true);
    };

    const isPseudoClick = (e: React.KeyboardEvent<HTMLAnchorElement>): boolean => e.key === 'Enter' || e.key === ' ';

    const menus = {
        style: (
            <Menu className="nav-menu">
                <MenuItem
                    icon="diagram-tree"
                    text="Graph"
                    onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                        e.preventDefault();
                        dispatch(changeStyle('graph'));
                    }}
                    onKeyDown={(e) => isPseudoClick(e) && dispatch(changeStyle('graph'))}
                />
                <MenuItem
                    icon="folder-open"
                    text="Directory"
                    onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                        e.preventDefault();
                        dispatch(changeStyle('directory'));
                    }}
                    onKeyDown={(e) => isPseudoClick(e) && dispatch(changeStyle('directory'))}
                />
            </Menu>
        ),
        download: (
            <Menu className="nav-menu">
                <MenuItem
                    icon="layout"
                    text="JSON"
                    onClick={exportJSON}
                    role="button"
                    onKeyDown={(e) => {
                        (e.key == 'Enter' || e.key == ' ') && exportJSON();
                    }}
                />
                <MenuItem
                    icon="graph"
                    text="DOT"
                    href={`data:attachment/text,${encodeURIComponent(dot ? dot : '')}`}
                    download={fileName ? `${fileName.split('.')[0].replace(/\s+/g, '_')}.dot` : ''}
                />
                <MenuItem
                    icon="square"
                    text="PNG"
                    onClick={exportPNG}
                    onKeyDown={(e) => {
                        (e.key == 'Enter' || e.key == ' ') && exportPNG(null);
                    }}
                />
                <MenuItem
                    icon="widget"
                    text="SVG"
                    onClick={exportSVG}
                    onKeyDown={(e) => {
                        (e.key == 'Enter' || e.key == ' ') && exportSVG(null);
                    }}
                />
            </Menu>
        ),
        help: (
            <Menu className="nav-menu">
                <MenuItem text="/view">
                    <div className="cmd-desc">
                        <div>
                            <u className="title">Desc.:</u> Command that changes the view mode.
                        </div>
                        <div>
                            <u className="title">Pattern:</u> /view {'<option>'}.
                        </div>
                        <div>
                            <u className="title">Option:</u> full, clustered and colored-full.
                        </div>
                    </div>
                </MenuItem>
                <MenuItem text="/select">
                    <div className="cmd-desc">
                        <div>
                            <u className="title">Desc.:</u> Command that selects a group of nodes.
                        </div>
                        <div>
                            <u className="title">Pattern:</u> /select {'<option>'} {'<argument>'}
                        </div>
                        <div>
                            <u className="title">Options:</u>
                            <div className="option">
                                1 - A list of node ids wrapped by brackets and separated by commas (and spaces if
                                wanted) (eg.: [1, 15, 6, 3]).
                            </div>
                            <div className="option">
                                2 - A range of node ids wrapped by brackets and separated by hyphen (and spaces if
                                wanted) (eg.: [4 - 15]). This range will include the last element.
                            </div>
                            <div className="option">
                                3 - A regex expression used to select all the nodes which the conclusion owns a match
                                (eg.: /\.*false\.*/ selects all the nodes with false anywhere in the conclusion).
                            </div>
                        </div>

                        <div>
                            <u className="title">Argument:</u> The argument can only be applied with the third option.
                            <br />
                            To search a match in the rule just insert the --r argument. The --c argument exists but the
                            /select will by default search in the conclusion.
                        </div>
                    </div>
                </MenuItem>
                <MenuItem text="/unselect">
                    <div className="cmd-desc">
                        <div>
                            <u className="title">Desc.:</u> Command that unselect all the nodes.
                        </div>
                        <div>
                            <u className="title">Pattern:</u> /unselect.
                        </div>
                    </div>
                </MenuItem>
                <MenuItem text="/color">
                    <div className="cmd-desc">
                        <div>
                            <u className="title">Desc.:</u> Command that changes the color of the current selected
                            nodes.
                        </div>
                        <div>
                            <u className="title">Pattern:</u> /color {'<option>'}.
                        </div>
                        <div>
                            <u className="title">Options:</u>
                            <div className="option">1 - A valid hex color notation (eg.: #A7B).</div>
                            <div className="option">
                                2 - A color name among: red🟥, orange🟧, yellow🟨, green🟩, blue🟦, purple🟪, brown🟫,
                                black⬛ and white⬜.
                            </div>
                        </div>
                        <div>
                            <u className="title">Prerequisites:</u> a group of nodes being selected.
                        </div>
                    </div>
                </MenuItem>
                <MenuItem text="/hide">
                    <div className="cmd-desc">
                        <div>
                            <u className="title">Desc.:</u> Command that try to fold (hide) a group of selected nodes.
                        </div>
                        <div>
                            <u className="title">Pattern:</u> /hide.
                        </div>
                        <div>
                            <u className="title">Prerequisites:</u> a group of nodes being selected.
                        </div>
                    </div>
                </MenuItem>
                <MenuItem text="/fold">
                    <div className="cmd-desc">
                        <div>
                            <u className="title">Desc.:</u> Command that fold all descendants of a specific node.
                        </div>
                        <div>
                            <u className="title">Pattern:</u> /fold {'<option>'}.
                        </div>
                        <div>
                            <u className="title">Option:</u> a valid node id.
                        </div>
                    </div>
                </MenuItem>
                <MenuItem text="/unfold">
                    <div className="cmd-desc">
                        <div>
                            <u className="title">Desc.:</u> Command that unfold a specific pi node.
                        </div>
                        <div>
                            <u className="title">Pattern:</u> /unfold {'<option>'}.
                        </div>
                        <div>
                            <u className="title">Option:</u> a valid pi node id.
                        </div>
                    </div>
                </MenuItem>
                <MenuItem text="/find">
                    <div className="cmd-desc">
                        <div>
                            <u className="title">Desc.:</u> Command that find a node and centralize the canvas at it.
                        </div>
                        <div>
                            <u className="title">Pattern:</u> /find {'<node number>'} {'<argument>'}.
                        </div>
                        <div>
                            <u className="title">Argument:</u> --s: find and select the node.
                        </div>
                    </div>
                </MenuItem>
            </Menu>
        ),
        examples: (
            <Menu className="nav-menu">
                {Object.keys(examples).map((ex, id) => {
                    return (
                        <MenuItem
                            key={id}
                            text={`Example ${id + 1}`}
                            onClick={(e) => runExample(e, ex, id)}
                            onKeyDown={(e) => isPseudoClick(e) && runExample(null, ex, id)}
                        />
                    );
                })}
            </Menu>
        ),
    };

    const tabIndex = inTutorial ? -1 : 0;

    const criticalWidth = 1350;
    return (
        <Navbar id="main-navbar">
            <Navbar.Group align={Alignment.LEFT}>
                <Navbar.Heading>
                    <b id="proof-visualizer-name">{windowSize.width >= criticalWidth ? 'Proof Visualizer' : 'PV'}</b>
                </Navbar.Heading>
                <Navbar.Divider />
                <Button
                    onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                        e.preventDefault();
                        openDialog('upload-proof');
                    }}
                    id="upload-proof-bt"
                    className="bp3-minimal"
                    icon="upload"
                    text={windowSize.width >= criticalWidth ? 'Upload Proof' : ''}
                    tabIndex={tabIndex}
                />
                <Popover2
                    content={fileName ? menus.examples : undefined}
                    placement="bottom-end"
                    modifiers={{ arrow: { enabled: isNotMozz } }}
                >
                    <Button
                        id="examples-bt"
                        className="bp3-minimal"
                        icon="manual"
                        text={windowSize.width >= criticalWidth ? 'Examples' : ''}
                        tabIndex={tabIndex}
                    />
                </Popover2>
                <Button
                    id="input-smt-bt"
                    className="bp3-minimal"
                    icon="code"
                    text={windowSize.width >= criticalWidth ? 'SMT Input' : ''}
                    onClick={() => setSmtDrawerIsOpen(true)}
                    tabIndex={tabIndex}
                />
            </Navbar.Group>

            <Navbar.Group align={Alignment.RIGHT}>
                {fileName ? (
                    <>
                        <Navbar.Heading id="file-name-title">{fileName}</Navbar.Heading>
                        <Navbar.Divider />
                        <Popover2
                            autoFocus={false}
                            enforceFocus={false}
                            content={renderMatchableCmd()}
                            isOpen={matchableCmdIsOpen}
                            disabled={matchableCmd.length === 0}
                            placement="bottom-end"
                            modifiers={{ arrow: { enabled: isNotMozz } }}
                        >
                            <InputGroup
                                id="command"
                                placeholder="/command"
                                value={command}
                                onChange={(e) => {
                                    setCommandId(0);
                                    lastCommands[0] = e.target.value;
                                    setLastCommands(lastCommands);
                                    setCommand(e.target.value);
                                    findMatchableCmd(e);
                                }}
                                onKeyDown={handleInputKeyDown}
                                rightElement={
                                    <Popover2
                                        content={menus.help}
                                        placement="bottom-end"
                                        modifiers={{ arrow: { enabled: isNotMozz } }}
                                    >
                                        <Button
                                            icon="help"
                                            className="bp3-minimal"
                                            onFocusCapture={(e) => inTutorial && e.target.blur()}
                                            tabIndex={-1}
                                        />
                                    </Popover2>
                                }
                                autoComplete="off"
                                tabIndex={tabIndex}
                            />
                        </Popover2>
                        <Button
                            style={{ marginLeft: '5px' }}
                            icon="play"
                            onClick={() => {
                                runCommands(command);
                                lastCommands.pop();
                                lastCommands.unshift(command);
                                lastCommands[0] = '';
                                setLastCommands(lastCommands);
                                setCommand('');
                            }}
                            onFocusCapture={(e) => inTutorial && e.target.blur()}
                            tabIndex={-1}
                        />
                        <Navbar.Divider />
                        <Popover2
                            content={fileName ? menus.style : undefined}
                            placement="bottom-end"
                            disabled={fileName ? false : true}
                            modifiers={{ arrow: { enabled: isNotMozz } }}
                        >
                            <Button
                                id="style-bt"
                                icon="presentation"
                                className="bp3-minimal"
                                text={windowSize.width >= criticalWidth ? 'Style' : ''}
                                disabled={fileName ? false : true}
                                tabIndex={tabIndex}
                            />
                        </Popover2>
                        <Button
                            id="visualizers-bt"
                            className="bp3-minimal"
                            icon="applications"
                            text={windowSize.width >= criticalWidth ? 'Visualizers' : ''}
                            disabled={fileName ? false : true}
                            onClick={() => setDrawerIsOpen(true)}
                            tabIndex={tabIndex}
                        />
                        <Popover2
                            content={fileName ? menus.download : undefined}
                            placement="bottom-end"
                            disabled={fileName ? false : true}
                            modifiers={{ arrow: { enabled: isNotMozz } }}
                        >
                            <Button
                                id="download-bt"
                                className="bp3-minimal"
                                icon="download"
                                text={windowSize.width >= criticalWidth ? 'Download' : ''}
                                disabled={fileName ? false : true}
                                tabIndex={tabIndex}
                            />
                        </Popover2>
                        <Button
                            className="bp3-minimal"
                            icon="learning"
                            text={windowSize.width >= criticalWidth ? 'Tutorial' : ''}
                            disabled={fileName ? false : true}
                            onClick={(e) => {
                                e.stopPropagation();
                                e.currentTarget.blur();
                                setInTutorial(!inTutorial);
                            }}
                            tabIndex={tabIndex}
                        />
                        <Navbar.Divider />
                    </>
                ) : null}

                <span id="switch-button-dark-theme">
                    <Switch
                        checked={useAppSelector(selectTheme)}
                        onChange={() => dispatch(toggle())}
                        tabIndex={tabIndex}
                    />
                    <Icon icon={darkTheme ? 'moon' : 'flash'}></Icon>
                </span>
            </Navbar.Group>
        </Navbar>
    );
};

function mapStateToProps(state: ReduxState, ownProps: NavbarProps) {
    return {
        ...ownProps,
        proof: selectProof(state),
        dot: selectDot(state),
        view: selectView(state),
        visualInfo: selectVisualInfo(state),
        hiddenNodes: selectHiddenNodes(state),
    };
}

const mapDispatchToProps = { hideNodes };

export default connect(mapStateToProps, mapDispatchToProps)(VisualizerNavbar);
