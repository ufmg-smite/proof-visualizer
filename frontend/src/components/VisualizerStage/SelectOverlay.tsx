import React, { useEffect, useMemo, useRef, useState } from 'react';
import { SelectOverlayProps } from '../../interfaces/interfaces';

import '../../scss/SelectOverlay.scss';
import { setSelectArea } from '../../store/features/externalCmd/externalCmd';
import { useAppDispatch } from '../../store/hooks';

const overlayColor = '#00000028';

const SelectOvelay: React.FC<SelectOverlayProps> = ({ isSelecting, setIsSelecting }: SelectOverlayProps) => {
    const isDraggingRef = useRef(false);
    const [isInverted, setIsInverted] = useState({ x: false, y: false });
    const [start, setStart] = useState({ x: 10, y: 10 });
    const [curPos, setCurPos] = useState({ x: 10, y: 10 });
    const dispatch = useAppDispatch();

    useEffect(() => {
        if (isSelecting) {
            document.body.addEventListener('mouseup', handleOutsideMouseUp);
        } else {
            document.body.removeEventListener('mouseup', handleOutsideMouseUp);
        }

        function handleOutsideMouseUp(e: MouseEvent) {
            if (isDraggingRef.current) {
                handleMouseUp(e);
            }
        }

        return () => {
            document.body.removeEventListener('mouseup', handleOutsideMouseUp);
        };
    }, [isSelecting]);

    // Make sure the component restart
    useEffect(() => {
        if (isSelecting) {
            isDraggingRef.current = false;
            setIsInverted({ x: false, y: false });
            setStart({ x: 10, y: 10 });
            setCurPos({ x: 10, y: 10 });
        }
    }, [isSelecting]);

    const style: any = useMemo(() => {
        return {
            opacity: isSelecting ? 1 : 0,
            pointerEvents: isSelecting ? 'all' : 'none',
        };
    }, [isSelecting]);

    const handleMouseDown = (e: React.MouseEvent) => {
        const { offsetX, offsetY } = e.nativeEvent;
        isDraggingRef.current = true;
        setStart({ x: offsetX, y: offsetY });
    };

    const handleMouseUp = (e: React.MouseEvent | MouseEvent) => {
        e.stopPropagation();
        // Turn off the selector
        setIsSelecting({ type: 'set', payload: false });

        // Call the selection
        let leftX = start.x,
            leftY = start.y,
            rightX = curPos.x,
            rightY = curPos.y;
        if (isInverted.x) {
            leftX = curPos.x;
            rightX = start.x;
        }
        if (isInverted.y) {
            leftY = curPos.y;
            rightY = start.y;
        }
        dispatch(setSelectArea({ upperL: { x: leftX, y: leftY }, lowerR: { x: rightX, y: rightY } }));
    };

    const handleMove = (e: React.MouseEvent) => {
        const { offsetX, offsetY } = e.nativeEvent;
        setCurPos({ x: offsetX, y: offsetY });

        if (isDraggingRef.current) {
            let xInverted = false,
                yInverted = false;
            if (start.x > offsetX) {
                xInverted = true;
            }
            if (start.y > offsetY) {
                yInverted = true;
            }
            setIsInverted({ x: xInverted, y: yInverted });
        }
    };

    const gridColumns = useMemo(() => {
        const difX = Math.abs(start.x - curPos.x);
        return isDraggingRef.current
            ? isInverted.x
                ? `${curPos.x}px ${difX}px 1fr`
                : `${start.x}px ${difX}px 1fr`
            : `${curPos.x}px 2px 1fr`;
    }, [curPos.x]);
    const gridRows = useMemo(() => {
        const difY = Math.abs(start.y - curPos.y);
        return isDraggingRef.current
            ? isInverted.y
                ? `${curPos.y}px ${difY}px 1fr`
                : `${start.y}px ${difY}px 1fr`
            : `${curPos.y}px 2px 1fr`;
    }, [curPos.y]);
    const color = useMemo(() => (isDraggingRef.current ? overlayColor : 'red'), [isDraggingRef.current]);

    return (
        <div
            className="select-overlay"
            style={{
                ...style,
                gridTemplateColumns: gridColumns,
                gridTemplateRows: gridRows,
            }}
            onMouseDown={handleMouseDown}
            onMouseUp={handleMouseUp}
            onMouseMoveCapture={handleMove}
            draggable={false}
            onDragStart={(e) => e.preventDefault()}
        >
            <div id="1" className="square" style={{ backgroundColor: overlayColor }}></div>
            <div id="2" className="square" style={{ backgroundColor: color }}></div>
            <div id="3" className="square" style={{ backgroundColor: overlayColor }}></div>
            <div id="4" className="square" style={{ backgroundColor: color }}></div>
            <div id="5" className="square" style={{ backgroundColor: color }}></div>
            <div id="6" className="square" style={{ backgroundColor: overlayColor }}></div>
            <div id="7" className="square" style={{ backgroundColor: color }}></div>
            <div id="8" className="square" style={{ backgroundColor: overlayColor }}></div>
        </div>
    );
};

export default SelectOvelay;
