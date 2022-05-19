import { Button, Divider, Icon } from '@blueprintjs/core';
import React, { useState } from 'react';
import { TutorialPopoverProps } from '../../interfaces/interfaces';
import { selectTheme } from '../../store/features/theme/themeSlice';
import { useAppSelector } from '../../store/hooks';

const TutorialPopover: React.FC<TutorialPopoverProps> = ({
    setIsOpen,
    nextTutorial,
    content,
    W,
    position,
}: TutorialPopoverProps) => {
    const [page, setPage] = useState(0);

    const darkTheme = useAppSelector(selectTheme);

    const renderPageBall = (): JSX.Element[] => {
        return content.map((_, id) => <div key={id} className={`page-ball ${id === page && 'page-on'}`} />);
    };

    const changePage = (type: string): void => {
        if (type === '>') setPage(page + 1);
        else setPage(page - 1);
    };

    return (
        <div className={darkTheme ? 'bp3-dark' : ''}>
            <div
                className="arrow-up"
                style={{
                    left: position.x + W / 2 - 4,
                    top: position.y - 7,
                    borderBottomColor: darkTheme ? 'rgb(30, 38, 44)' : 'rgb(255,255,255)',
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
                    <p className="content">{content[page]}</p>
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
