import React, { useEffect, useMemo, useReducer, useRef, useState } from 'react';
import { SelectOverlayProps } from '../../interfaces/interfaces';

import '../../scss/SelectOverlay.scss';
import { setSelectArea } from '../../store/features/externalCmd/externalCmd';
import { useAppDispatch } from '../../store/hooks';

const overlayColor = '#00000028';

const SelectOvelay: React.FC<SelectOverlayProps> = ({
    isSelecting,
    selectMode,
    setIsSelecting,
}: SelectOverlayProps) => {
    const [, forceUpdate] = useReducer((x) => x + 1, 0);
    const isDraggingRef = useRef(false);
    const startRef = useRef({ x: 10, y: 10 });
    const posRef = useRef({ x: 10, y: 10 });
    const [isInverted, setIsInverted] = useState({ x: false, y: false });
    const [selectColor, setSelectColor] = useState(selectMode ? 'blue' : 'red');
    const [color, setColor] = useState(isDraggingRef.current ? overlayColor : selectColor);
    const dispatch = useAppDispatch();

    useEffect(() => {
        const newSelectColor = selectMode ? 'blue' : 'red';
        setSelectColor(newSelectColor);
        setColor(isDraggingRef.current ? overlayColor : newSelectColor);
    }, [selectMode, isDraggingRef.current]);

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
            startRef.current = { x: 10, y: 10 };
            posRef.current = { x: 10, y: 10 };
            setIsInverted({ x: false, y: false });
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
        startRef.current = { x: offsetX, y: offsetY };
        forceUpdate();
    };

    const handleMouseUp = (e: React.MouseEvent | MouseEvent) => {
        e.stopPropagation();
        // Turn off the selector
        setIsSelecting({ type: 'set', payload: { value: false, key: 'n' } });

        // Call the selection
        let leftX = startRef.current.x,
            leftY = startRef.current.y,
            rightX = posRef.current.x,
            rightY = posRef.current.y;
        if (isInverted.x) {
            leftX = posRef.current.x;
            rightX = startRef.current.x;
        }
        if (isInverted.y) {
            leftY = posRef.current.y;
            rightY = startRef.current.y;
        }
        dispatch(
            setSelectArea({
                type: selectMode,
                square: { upperL: { x: leftX, y: leftY }, lowerR: { x: rightX, y: rightY } },
            }),
        );
    };

    const handleMove = (e: React.MouseEvent) => {
        const { offsetX, offsetY } = e.nativeEvent;
        posRef.current = { x: offsetX, y: offsetY };

        if (isDraggingRef.current) {
            let xInverted = false,
                yInverted = false;
            if (startRef.current.x > offsetX) {
                xInverted = true;
            }
            if (startRef.current.y > offsetY) {
                yInverted = true;
            }
            setIsInverted({ x: xInverted, y: yInverted });
        }
        forceUpdate();
    };

    const gridColumns = useMemo(() => {
        const difX = Math.abs(startRef.current.x - posRef.current.x);
        return isDraggingRef.current
            ? isInverted.x
                ? `${posRef.current.x}px ${difX}px 1fr`
                : `${startRef.current.x}px ${difX}px 1fr`
            : `${posRef.current.x}px 2px 1fr`;
    }, [posRef.current]);
    const gridRows = useMemo(() => {
        const difY = Math.abs(startRef.current.y - posRef.current.y);
        return isDraggingRef.current
            ? isInverted.y
                ? `${posRef.current.y}px ${difY}px 1fr`
                : `${startRef.current.y}px ${difY}px 1fr`
            : `${posRef.current.y}px 2px 1fr`;
    }, [posRef.current]);

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
            <div id="2" className="square" style={{ backgroundColor: color, borderBottomColor: selectColor }}></div>
            <div id="3" className="square" style={{ backgroundColor: overlayColor }}></div>
            <div id="4" className="square" style={{ backgroundColor: color, borderRightColor: selectColor }}></div>
            <div id="5" className="square" style={{ backgroundColor: color, borderLeftColor: selectColor }}></div>
            <div id="6" className="square" style={{ backgroundColor: overlayColor }}></div>
            <div id="7" className="square" style={{ backgroundColor: color, borderTopColor: selectColor }}></div>
            <div id="8" className="square" style={{ backgroundColor: overlayColor }}></div>
        </div>
    );
};

export default SelectOvelay;
