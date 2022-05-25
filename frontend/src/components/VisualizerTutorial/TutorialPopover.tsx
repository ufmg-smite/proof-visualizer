import { Button, Divider, Icon } from '@blueprintjs/core';
import React, { useEffect, useState } from 'react';
import { TutorialPopoverProps } from '../../interfaces/interfaces';
import { selectTheme } from '../../store/features/theme/themeSlice';
import { useAppSelector } from '../../store/hooks';

const TutorialPopover: React.FC<TutorialPopoverProps> = ({
    setIsOpen,
    nextTutorial,
    stage,
    content,
    W,
    position,
}: TutorialPopoverProps) => {
    const [page, setPage] = useState(0);

    const darkTheme = useAppSelector(selectTheme);

    const renderPageBall = (): JSX.Element[] => {
        return content.map((_, id) => (
            <div key={id} className={`page-ball ${id === page && (darkTheme ? 'page-on' : 'page-on-light')}`} />
        ));
    };

    const changePage = (type: string): void => {
        if (type === '>') setPage(page + 1);
        else setPage(page - 1);
    };

    useEffect(() => {
        function handleEsc(e: KeyboardEvent): void {
            e.stopPropagation();
            if (e.key === 'Escape') {
                setIsOpen(false);
            }
        }
        window.addEventListener('keydown', handleEsc, false);

        return () => {
            window.removeEventListener('keydown', handleEsc, false);
        };
    }, []);

    const insertAnchors = (text: string): (JSX.Element | string)[] => {
        const list: (JSX.Element | string)[] = [];

        let i = -1,
            last = 0;
        const positions = [0, 0, 0];
        for (let j = 0; j < text.length; j++) {
            if (text[j] === '\0') {
                i++;
                positions[i] = j;
            }
            if (i === 2) {
                list.push(text.substring(last, positions[0]));
                const name = text.substring(positions[0] + 1, positions[1]);
                const link = text.substring(positions[1] + 1, positions[2]);
                list.push(
                    <a href={link} target="_blank" rel="noreferrer">
                        {name}
                    </a>,
                );

                last = positions[2] + 1;
                i = -1;
            }
        }
        list.push(text.substring(last, text.length));

        return list;
    };

    return (
        <div className={darkTheme ? 'bp3-dark' : ''}>
            <div
                className="arrow-up"
                style={{
                    left: position.tW,
                    top: position.y - 7,
                    borderBottomColor: darkTheme ? 'rgb(48, 65, 71)' : 'rgb(255,255,255)',
                }}
            />
            <div
                className="arrow-up arrow-2"
                style={{
                    left: position.tW - 2,
                    top: position.y - 9,
                    borderBottomColor: darkTheme ? '#bdbdbd' : 'rgba(71, 64, 64, 0.281)',
                }}
            />
            <div className="tutorial-popover bp3-dialog" style={{ width: W, left: position.x, top: position.y }}>
                <div className="bp3-dialog-header">
                    <div className="cur-page">{renderPageBall()}</div>
                    <Icon icon="small-cross" size={20} onClick={() => setIsOpen(false)} />
                </div>
                <body>
                    {page > 0 && (
                        <div
                            className="next-page regress"
                            onClick={(e) => {
                                e.stopPropagation();
                                changePage('<');
                            }}
                        >
                            {'<'}
                        </div>
                    )}
                    <p className="content">{stage ? content[page] : insertAnchors(content[page])}</p>
                    {page < content.length - 1 && (
                        <div
                            className="next-page progress"
                            onClick={(e) => {
                                e.stopPropagation();
                                changePage('>');
                            }}
                        >
                            {'>'}
                        </div>
                    )}
                </body>
                {page === content.length - 1 && (
                    <>
                        <Divider style={{ backgroundColor: darkTheme ? 'white' : '' }} />
                        <div className="bp3-dialog-footer">
                            <Button
                                text="Next"
                                onClick={(e) => {
                                    e.stopPropagation();
                                    nextTutorial();
                                    setPage(0);
                                }}
                            />
                        </div>
                    </>
                )}
            </div>
        </div>
    );
};

export default TutorialPopover;
